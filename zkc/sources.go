package zkc

import (
	_ "embed"
	"strings"
)

// e6Library is the E6 arithmetic library, see e6.zkc.
//
//go:embed e6.zkc
var e6Library string

// E6Native declares e6_mul #[native] instead of #[inline]: E6MulGadget then
// supplies its constraints, one row per multiplication (see Gadgets).
var E6Native = true

// E6Source returns the E6 library, with e6_mul native if E6Native is set.
func E6Source() string {
	if !E6Native {
		return e6Library
	}
	const inlined = "#[inline]\nfn e6_mul("
	if !strings.Contains(e6Library, inlined) {
		panic("e6.zkc: e6_mul is not declared #[inline]")
	}
	return strings.Replace(e6Library, inlined, "#[native]\nfn e6_mul(", 1)
}
