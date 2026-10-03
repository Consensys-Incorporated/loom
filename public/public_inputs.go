package public

import (
	"sort"

	"github.com/consensys/gnark-crypto/field/koalabear"
	"github.com/consensys/gnark-crypto/field/koalabear/extensions"
	"github.com/consensys/loom/field"
	fieldhash "github.com/consensys/loom/internal/hash"
)

// DomainTag starts the transcript encoding of the public inputs, and of each
// name and module in it.
const DomainTag uint64 = 0x50554249 // "PUBI"

type Input struct {
	Module  string
	Entries []Entry
}

type Entry struct {
	Idx      int
	Field    field.Kind
	Value    koalabear.Element
	ValueExt extensions.E6
}

type Inputs map[string]Input

func (e *Entry) SetBase(v koalabear.Element) {
	e.Field = field.Base
	e.Value.Set(&v)
	e.ValueExt = fieldhash.LiftBaseToExt(v)
}

func (e *Entry) SetExt(v extensions.E6) {
	e.Field = field.Ext
	e.ValueExt.Set(&v)
}

func (e Entry) ExtValue() extensions.E6 {
	if e.Field == field.Ext {
		return e.ValueExt
	}
	return fieldhash.LiftBaseToExt(e.Value)
}

// TranscriptElements returns a deterministic field-element encoding of the
// public statement values suitable for Fiat-Shamir binding.
func (inputs Inputs) TranscriptElements() []koalabear.Element {
	names := make([]string, 0, len(inputs))
	for name := range inputs {
		names = append(names, name)
	}
	sort.Strings(names)

	res := make([]koalabear.Element, 0)
	res = append(res, fieldhash.NewElement(DomainTag), fieldhash.NewElement(uint64(len(names))))
	for _, name := range names {
		input := inputs[name]
		res = append(res, fieldhash.StringToElements(DomainTag, name)...)
		res = append(res, fieldhash.StringToElements(DomainTag, input.Module)...)

		entries := input.SortedEntries()

		res = append(res, fieldhash.NewElement(uint64(len(entries))))
		for _, entry := range entries {
			res = append(res, fieldhash.NewElement(uint64(entry.Idx)), fieldhash.NewElement(uint64(entry.Field)))
			res = appendEntryValueElements(res, entry)
		}
	}

	return res
}

// SortedEntries returns the entries in their transcript order: by index, then
// field, then value.
func (input Input) SortedEntries() []Entry {
	entries := append([]Entry(nil), input.Entries...)
	sort.Slice(entries, func(i, j int) bool {
		if entries[i].Idx != entries[j].Idx {
			return entries[i].Idx < entries[j].Idx
		}
		if entries[i].Field != entries[j].Field {
			return entries[i].Field < entries[j].Field
		}
		return compareEntryValues(entries[i], entries[j]) < 0
	})
	return entries
}

func appendEntryValueElements(dst []koalabear.Element, entry Entry) []koalabear.Element {
	if entry.Field == field.Ext {
		return fieldhash.AppendExtElements(dst, entry.ValueExt)
	}
	return append(dst, entry.Value)
}

func compareEntryValues(a, b Entry) int {
	aVals := entryValueElements(a)
	bVals := entryValueElements(b)
	for i := range aVals {
		if cmp := aVals[i].Cmp(&bVals[i]); cmp != 0 {
			return cmp
		}
	}
	return 0
}

func entryValueElements(entry Entry) []koalabear.Element {
	if entry.Field == field.Ext {
		return fieldhash.ExtToElements(entry.ValueExt)
	}
	return []koalabear.Element{entry.Value}
}
