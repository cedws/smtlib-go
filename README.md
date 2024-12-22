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
	"fmt"
	"os"

	. "github.com/cedws/smtlib-go"
)

func main() {
	// Declare the variables
	nodeA := &Variable{Name: "node_A"}
	nodeB := &Variable{Name: "node_B"}
	nodeC := &Variable{Name: "node_C"}
	nodeD := &Variable{Name: "node_D"}
	nodeE := &Variable{Name: "node_E"}
	nodeF := &Variable{Name: "node_F"}

	// Create the problem with initial capacity of 32
	problem := make(Problem, 0, 32)

	problem.Add(&DeclareFun{Name: "node_A", Type: "Bool"})
	problem.Add(&DeclareFun{Name: "node_B", Type: "Bool"})
	problem.Add(&DeclareFun{Name: "node_C", Type: "Bool"})
	problem.Add(&DeclareFun{Name: "node_D", Type: "Bool"})
	problem.Add(&DeclareFun{Name: "node_E", Type: "Bool"})
	problem.Add(&DeclareFun{Name: "node_F", Type: "Bool"})

	// Add tree constraints
	problem.Add(&Assert{Expression: &Implies{Antecedent: nodeD, Consequent: &Or{Left: nodeA, Right: nodeB}}})
	problem.Add(&Assert{Expression: &Implies{Antecedent: nodeE, Consequent: &Or{Left: nodeB, Right: nodeC}}})
	problem.Add(&Assert{Expression: &Implies{Antecedent: nodeF, Consequent: &Or{Left: nodeD, Right: nodeE}}})

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
		maximiseTerms = append(maximiseTerms, &Ite{
			Condition: &Variable{Name: node},
			TrueExpr:  &Variable{Name: fmt.Sprintf("%d", value)},
			FalseExpr: &Variable{Name: "0"},
		})
	}

	problem.Add(&Maximize{
		Objective: Sum(
			maximiseTerms,
		),
	})

	// Initialise terms
	iteTerms := []Expression{
		&Ite{Condition: nodeA, TrueExpr: &Variable{Name: "1"}, FalseExpr: &Variable{Name: "0"}},
		&Ite{Condition: nodeB, TrueExpr: &Variable{Name: "1"}, FalseExpr: &Variable{Name: "0"}},
		&Ite{Condition: nodeC, TrueExpr: &Variable{Name: "1"}, FalseExpr: &Variable{Name: "0"}},
		&Ite{Condition: nodeD, TrueExpr: &Variable{Name: "1"}, FalseExpr: &Variable{Name: "0"}},
		&Ite{Condition: nodeE, TrueExpr: &Variable{Name: "1"}, FalseExpr: &Variable{Name: "0"}},
		&Ite{Condition: nodeF, TrueExpr: &Variable{Name: "1"}, FalseExpr: &Variable{Name: "0"}},
	}

	maxNodes := 4

	problem.Add(&Assert{
		Expression: &LessThanOrEqual{
			Sum(iteTerms),
			&Variable{Name: fmt.Sprint(maxNodes)},
		},
	})

	problem.Add(&CheckSat{})
	problem.Add(&GetModel{})

	problem.WriteTo(os.Stdout)
}
```
