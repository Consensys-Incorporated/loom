package fibonacci

import (
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
)

func PrepareFibonacciModule(N int) board.Module {
	fibonacciModule := board.NewModule("fibonacci")
	fibonacciModule.N = N
	C := expr.Col("A", expr.WithShift(1)).Sub(expr.Col("B"))
	fibonacciModule.AssertZeroExceptAt(C, N-1)
	C = expr.Col("B", expr.WithShift(1)).Sub(expr.Col("C"))
	fibonacciModule.AssertZeroExceptAt(C, N-1)
	C = expr.Col("C").Sub(expr.Col("A")).Sub(expr.Col("B"))
	fibonacciModule.AssertZero(C)
	return fibonacciModule
}
