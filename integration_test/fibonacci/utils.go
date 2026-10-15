package fibonacci

import (
	"github.com/consensys/loom/board"
	"github.com/consensys/loom/expr"
)

func PrepareFibonacciModule(N int) board.Module {
	fibonacciModule := board.NewModule("fibonacci")
	fibonacciModule.N = N
	fibonacciModule.AssertZeroExceptAt(expr.Col("A", expr.WithShift(1)).Sub(expr.Col("B")), N-1)
	fibonacciModule.AssertZeroExceptAt(expr.Col("B", expr.WithShift(1)).Sub(expr.Col("C")), N-1)
	fibonacciModule.AssertZero(expr.Col("C").Sub(expr.Col("A")).Sub(expr.Col("B")))
	return fibonacciModule
}
