# zkc testdata

`zkc_XX.zkc` are the sources, `zkc_XX.bin` their compiled binaries. If reading
a binary fails, zkc was updated and its format changed: regenerate them with

    go test ./integration_test/zkc -run FromBinary -update
