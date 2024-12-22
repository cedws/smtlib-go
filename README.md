# smtlib-go

Go library for generating [SMT-LIB](https://smt-lib.org/) problem S-expressions.

## Example

This code generates an SMT-LIB problem to stdout which can then be passed to a solver like Z3.

```
// Optimise for the best path (highest value) in the tree given N nodes starting at the bottom with A, B, or C
// Node values are 10, 20, 30, 40, 50, 60 for A, B, C, D, E, F respectively

// Correct solution is C, E, F for maxNodes of 3
// Correct solution is B, D, E, F for maxNodes of 4

/*
	  F
	 D E
	A B C
*/
```

```go
package main

import (
	"os"

	. "github.com/cedws/smtlib-go"
)

func main() {
	// Declare the variables
	nodeA := Literal("node_A")
	nodeB := Literal("node_B")
	nodeC := Literal("node_C")
	nodeD := Literal("node_D")
	nodeE := Literal("node_E")
	nodeF := Literal("node_F")

	// Create the problem with initial capacity of 32
	problem := make(Problem, 0, 32)

	problem.Add(DeclareFun{Name: "node_A", Type: "Bool"})
	problem.Add(DeclareFun{Name: "node_B", Type: "Bool"})
	problem.Add(DeclareFun{Name: "node_C", Type: "Bool"})
	problem.Add(DeclareFun{Name: "node_D", Type: "Bool"})
	problem.Add(DeclareFun{Name: "node_E", Type: "Bool"})
	problem.Add(DeclareFun{Name: "node_F", Type: "Bool"})

	// Add tree constraints
	problem.Add(Assert{Expression: Implies{Antecedent: nodeD, Consequent: Or{Left: nodeA, Right: nodeB}}})
	problem.Add(Assert{Expression: Implies{Antecedent: nodeE, Consequent: Or{Left: nodeB, Right: nodeC}}})
	problem.Add(Assert{Expression: Implies{Antecedent: nodeF, Consequent: Or{Left: nodeD, Right: nodeE}}})

	nodeValues := map[string]int{
		"node_A": 10,
		"node_B": 20,
		"node_C": 30,
		"node_D": 40,
		"node_E": 50,
		"node_F": 60,
	}

	var maximiseTerms []Expression

	for node, value := range nodeValues {
		maximiseTerms = append(maximiseTerms, Ite{
			Condition: Literal(node),
			TrueExpr:  Literal(value),
			FalseExpr: Literal(0),
		})
	}

	problem.Add(Maximize{
		Objective: Sum(
			maximiseTerms,
		),
	})

	// Initialise terms
	iteTerms := []Expression{
		Ite{Condition: nodeA, TrueExpr: Literal(1), FalseExpr: Literal(0)},
		Ite{Condition: nodeB, TrueExpr: Literal(1), FalseExpr: Literal(0)},
		Ite{Condition: nodeC, TrueExpr: Literal(1), FalseExpr: Literal(0)},
		Ite{Condition: nodeD, TrueExpr: Literal(1), FalseExpr: Literal(0)},
		Ite{Condition: nodeE, TrueExpr: Literal(1), FalseExpr: Literal(0)},
		Ite{Condition: nodeF, TrueExpr: Literal(1), FalseExpr: Literal(0)},
	}

	// Generate best solutions up to 6 max nodes
	for maxNodes := range 6 {
		problem.Add(Push{})

		problem.Add(Assert{
			Expression: LessThanOrEqual{
				Sum(iteTerms),
				Literal(maxNodes + 1),
			},
		})

		problem.Add(CheckSat{})
		problem.Add(GetModel{})

		problem.Add(Pop{})
	}

	problem.WriteTo(os.Stdout)
}
```
