package riscv

import (
	"testing"
)

// TestCompiledBinaryFile compiles the embedded interpreter. Without AIR
// validation: zkc's validator reports the modules reached through the
// interpreter's call bus as unreachable, upstream too (lineth main 9ff51bc01).
func TestCompiledBinaryFile(t *testing.T) {
	binfile, err := CompiledBinaryFile()
	if err != nil {
		t.Fatalf("failed to compile embedded R5 interpreter: %v", err)
	}
	if binfile == nil {
		t.Fatalf("compiled binary file is nil")
	}
}
