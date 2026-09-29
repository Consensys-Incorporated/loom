package zkc

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"

	zkcv "github.com/consensys/loom/integration_test/zkc_verifier"
)

// writeZkc writes zkc sources to a temporary directory and returns the paths.
func writeZkc(t *testing.T, sources map[string]string) []string {
	t.Helper()
	dir := t.TempDir()
	var paths []string
	for name, src := range sources {
		p := filepath.Join(dir, name)
		if err := os.WriteFile(p, []byte(src), 0o600); err != nil {
			t.Fatal(err)
		}
		paths = append(paths, p)
	}
	return paths
}

// assertForms are candidate encodings of 24 equality checks between xs[2i]
// and xs[2i+1].
func assertForms() map[string]string {
	var inline, calls, fparams, fargs strings.Builder
	for i := range 24 {
		fmt.Fprintf(&inline, "    if (xs[%d] as 𝔽) != (xs[%d] as 𝔽) { fail }\n", 2*i, 2*i+1)
		fmt.Fprintf(&calls, "    assert_eq(xs[%d] as 𝔽, xs[%d] as 𝔽)\n", 2*i, 2*i+1)
		fmt.Fprintf(&fparams, "a%d:𝔽, b%d:𝔽", i, i)
		fmt.Fprintf(&fargs, "xs[%d] as 𝔽, xs[%d] as 𝔽", 2*i, 2*i+1)
		if i < 23 {
			fparams.WriteString(", ")
			fargs.WriteString(", ")
		}
	}
	var fbody strings.Builder
	for i := range 24 {
		fmt.Fprintf(&fbody, "    if a%d != b%d { fail }\n", i, i)
	}
	header := "input xs(address:u16) -> (w:u32)\n\nfn main() {\n    for i:u16 = 0; i < 2; i = i + 1 {\n        check(i)\n    }\n}\n\n"
	return map[string]string{
		"A_inline_if": header + "fn check(k:u16) {\n" + inline.String() + "}\n",
		"B_assert_fn": header + "fn check(k:u16) {\n" + calls.String() + "}\n\n" +
			"fn assert_eq(a:𝔽, b:𝔽) {\n    if a != b { fail }\n}\n",
		"C_felt_params": header + "fn check(k:u16) {\n    check24(" + fargs.String() + ")\n}\n\n" +
			"fn check24(" + fparams.String() + ") {\n" + fbody.String() + "}\n",
	}
}

func xsInput(tamper bool) []byte {
	words := make([]uint32, 48)
	for i := range 24 {
		words[2*i] = uint32(1000 + i)
		words[2*i+1] = uint32(1000 + i)
	}
	if tamper {
		words[17]++
	}
	var sb strings.Builder
	sb.WriteString("0x")
	for _, w := range words {
		fmt.Fprintf(&sb, "%08x", w)
	}
	return []byte(fmt.Sprintf(`{"xs": "%s"}`, sb.String()))
}

// TestAssertForms records which assertion encodings zkc v1.2.32 compiles and
// proves, and that each rejects a wrong input.
func TestAssertForms(t *testing.T) {
	for name, src := range assertForms() {
		t.Run(name, func(t *testing.T) {
			files := writeZkc(t, map[string]string{"main.zkc": src})
			run := func(tamper bool) (err error) {
				defer func() {
					if r := recover(); r != nil {
						err = fmt.Errorf("panic: %v", r)
					}
				}()
				_, err = zkcv.Run(xsInput(tamper), files...)
				return err
			}
			if err := run(false); err != nil {
				t.Fatalf("valid input: %v", err)
			}
			if err := run(true); err == nil {
				t.Fatal("tampered input accepted")
			}
		})
	}
}
