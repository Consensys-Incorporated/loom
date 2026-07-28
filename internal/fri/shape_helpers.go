// Copyright Consensys Software Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with
// the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0

package fri

import (
	"fmt"
	"sort"
)

func validateBatchShifts(batches []Batch, shifts []BatchShifts) error {
	sizes, err := groupNativeSizesFromBatches(batches)
	if err != nil {
		return err
	}
	if len(shifts) != len(batches) {
		return fmt.Errorf("fri: shifts has %d entries, batches has %d", len(shifts), len(batches))
	}
	for b, batch := range batches {
		if len(shifts[b]) != len(batch) {
			return fmt.Errorf("fri: shifts[%d] has %d Groups, batches[%d] has %d", b, len(shifts[b]), b, len(batch))
		}
		for g, group := range batch {
			gShifts := shifts[b][g]
			if len(gShifts.Base) != len(group.Base) {
				return fmt.Errorf("fri: shifts[%d][%d].Base has %d entries, batches[%d][%d].Base has %d", b, g, len(gShifts.Base), b, g, len(group.Base))
			}
			if len(gShifts.Ext) != len(group.Ext) {
				return fmt.Errorf("fri: shifts[%d][%d].Ext has %d entries, batches[%d][%d].Ext has %d", b, g, len(gShifts.Ext), b, g, len(group.Ext))
			}
		}
	}
	return validateBatchShiftsFromSizes(sizes, shifts)
}

func sizesDescFromBatches(batches []Batch) ([]int, error) {
	sizes, err := groupNativeSizesFromBatches(batches)
	if err != nil {
		return nil, err
	}
	return sizesDescFromSizes(sizes), nil
}

func groupNativeSizesFromBatches(batches []Batch) ([][]int, error) {
	sizes := make([][]int, len(batches))
	for b, batch := range batches {
		sizes[b] = make([]int, len(batch))
		seen := make(map[int]struct{}, len(batch))
		for g, group := range batch {
			N, err := groupNativeSize(group)
			if err != nil {
				return nil, fmt.Errorf("fri: batches[%d][%d]: %w", b, g, err)
			}
			if _, dup := seen[N]; dup {
				return nil, fmt.Errorf("fri: batch %d has duplicate Group size %d at index %d", b, N, g)
			}
			seen[N] = struct{}{}
			sizes[b][g] = N
		}
	}
	return sizes, nil
}

func validateBatchShiftsFromShapes(shapes []BatchShapes, shifts []BatchShifts, rate uint64) error {
	sizes, err := groupNativeSizesFromShapes(shapes, rate)
	if err != nil {
		return err
	}
	if len(shifts) != len(shapes) {
		return fmt.Errorf("fri: shifts has %d entries, shapes has %d", len(shifts), len(shapes))
	}
	for b, batchShapes := range shapes {
		if len(shifts[b]) != len(batchShapes) {
			return fmt.Errorf("fri: shifts[%d] has %d Groups, shapes[%d] has %d", b, len(shifts[b]), b, len(batchShapes))
		}
		for g, gs := range batchShapes {
			gShifts := shifts[b][g]
			if len(gShifts.Base) != gs.BaseWidth {
				return fmt.Errorf("fri: shifts[%d][%d].Base has %d entries, shapes[%d][%d].BaseWidth=%d", b, g, len(gShifts.Base), b, g, gs.BaseWidth)
			}
			if len(gShifts.Ext) != gs.ExtWidth {
				return fmt.Errorf("fri: shifts[%d][%d].Ext has %d entries, shapes[%d][%d].ExtWidth=%d", b, g, len(gShifts.Ext), b, g, gs.ExtWidth)
			}
		}
	}
	return validateBatchShiftsFromSizes(sizes, shifts)
}

func sizesDescFromShapes(shapes []BatchShapes, rate uint64) ([]int, error) {
	sizes, err := groupNativeSizesFromShapes(shapes, rate)
	if err != nil {
		return nil, err
	}
	return sizesDescFromSizes(sizes), nil
}

func groupNativeSizesFromShapes(shapes []BatchShapes, rate uint64) ([][]int, error) {
	if rate == 0 || rate&(rate-1) != 0 {
		return nil, fmt.Errorf("fri: rate %d must be a positive power of two", rate)
	}
	sizes := make([][]int, len(shapes))
	for b, batchShapes := range shapes {
		sizes[b] = make([]int, len(batchShapes))
		seen := make(map[int]struct{}, len(batchShapes))
		for g, gs := range batchShapes {
			if gs.Rows <= 0 {
				return nil, fmt.Errorf("fri: shapes[%d][%d].Rows=%d must be positive", b, g, gs.Rows)
			}
			rows := uint64(gs.Rows)
			if rows%rate != 0 {
				return nil, fmt.Errorf("fri: shapes[%d][%d].Rows=%d not a multiple of rate", b, g, gs.Rows)
			}
			N := int(rows / rate)
			if N <= 0 || N&(N-1) != 0 {
				return nil, fmt.Errorf("fri: shapes[%d][%d] yields N=%d (not a positive power of two)", b, g, N)
			}
			if _, dup := seen[N]; dup {
				return nil, fmt.Errorf("fri: batch %d has duplicate Group size %d at index %d", b, N, g)
			}
			seen[N] = struct{}{}
			sizes[b][g] = N
		}
	}
	return sizes, nil
}

func validateBatchShiftsFromSizes(sizes [][]int, shifts []BatchShifts) error {
	if len(shifts) != len(sizes) {
		return fmt.Errorf("fri: shifts has %d entries, sizes has %d", len(shifts), len(sizes))
	}
	for b, batchSizes := range sizes {
		if len(shifts[b]) != len(batchSizes) {
			return fmt.Errorf("fri: shifts[%d] has %d Groups, sizes[%d] has %d", b, len(shifts[b]), b, len(batchSizes))
		}
		for g, N := range batchSizes {
			if N <= 0 || N&(N-1) != 0 {
				return fmt.Errorf("fri: sizes[%d][%d]=%d is not a positive power of two", b, g, N)
			}
			if err := validatePolyShifts(b, g, "Base", N, shifts[b][g].Base); err != nil {
				return err
			}
			if err := validatePolyShifts(b, g, "Ext", N, shifts[b][g].Ext); err != nil {
				return err
			}
		}
	}
	return nil
}

func validatePolyShifts(batchIdx, groupIdx int, rail string, N int, polyShifts [][]int) error {
	for polyIdx, ss := range polyShifts {
		if len(ss) == 0 {
			return fmt.Errorf("fri: shifts[%d][%d].%s[%d] has empty shift list", batchIdx, groupIdx, rail, polyIdx)
		}
		seen := make(map[int]int, len(ss))
		for _, s := range ss {
			normalized := normalizeShift(s, N)
			if prev, ok := seen[normalized]; ok {
				if prev == s {
					return fmt.Errorf("fri: shifts[%d][%d].%s[%d] has duplicate shift %d", batchIdx, groupIdx, rail, polyIdx, s)
				}
				return fmt.Errorf("fri: shifts[%d][%d].%s[%d] has duplicate shift modulo %d: %d and %d", batchIdx, groupIdx, rail, polyIdx, N, prev, s)
			}
			seen[normalized] = s
		}
	}
	return nil
}

func sizesDescFromSizes(sizes [][]int) []int {
	sizeSet := make(map[int]struct{})
	for _, batchSizes := range sizes {
		for _, N := range batchSizes {
			sizeSet[N] = struct{}{}
		}
	}
	sizesDesc := make([]int, 0, len(sizeSet))
	for N := range sizeSet {
		sizesDesc = append(sizesDesc, N)
	}
	sort.Sort(sort.Reverse(sort.IntSlice(sizesDesc)))
	return sizesDesc
}
