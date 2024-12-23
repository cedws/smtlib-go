package smtlib

import (
	"os"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
)

func readTestData(f string) string {
	data, err := os.ReadFile(f)
	if err != nil {
		panic(err)
	}
	s := string(data)
	s = strings.ReplaceAll(s, "\r\n", "\n")
	s = strings.TrimSuffix(s, "\n")
	return s
}

func TestAnd(t *testing.T) {
	s := And{
		Left:  Literal("node_A"),
		Right: Literal("node_B"),
	}
	assert.Equal(
		t,
		readTestData("testdata/and.smt2"),
		s.StringIndent(0),
		"expected strings to match",
	)
}

func TestOr(t *testing.T) {
	s := Or{
		Left:  Literal("node_A"),
		Right: Literal("node_B"),
	}
	assert.Equal(
		t,
		readTestData("testdata/or.smt2"),
		s.StringIndent(0),
		"expected strings to match",
	)
}

func TestNot(t *testing.T) {
	s := Not{
		Operand: Literal("node_A"),
	}
	assert.Equal(
		t,
		readTestData("testdata/not.smt2"),
		s.StringIndent(0),
		"expected strings to match",
	)
}

func TestImplies(t *testing.T) {
	s := Implies{
		Antecedent: Literal("node_A"),
		Consequent: Literal("node_B"),
	}
	assert.Equal(
		t,
		readTestData("testdata/implies.smt2"),
		s.StringIndent(0),
		"expected strings to match",
	)
}

func TestIte(t *testing.T) {
	s := Ite{
		Condition: Literal("node_A"),
		TrueExpr:  Literal(1),
		FalseExpr: Literal(0),
	}
	assert.Equal(
		t,
		readTestData("testdata/ite.smt2"),
		s.StringIndent(0),
		"expected strings to match",
	)
}

func TestSum(t *testing.T) {
	t.Run("One_Term", func(t *testing.T) {
		s := Sum([]Expression{
			Ite{
				Condition: Literal("node_A"),
				TrueExpr:  Literal(1),
				FalseExpr: Literal(0),
			},
		})
		assert.Equal(
			t,
			readTestData("testdata/sum_one_term.smt2"),
			s.StringIndent(0),
			"expected strings to match",
		)
	})

	t.Run("Three_Terms", func(t *testing.T) {
		s := Sum([]Expression{
			Ite{
				Condition: Literal("node_A"),
				TrueExpr:  Literal(1),
				FalseExpr: Literal(0),
			},
			Ite{
				Condition: Literal("node_B"),
				TrueExpr:  Literal(1),
				FalseExpr: Literal(0),
			},
			Ite{
				Condition: Literal("node_C"),
				TrueExpr:  Literal(1),
				FalseExpr: Literal(0),
			},
		})
		assert.Equal(
			t,
			readTestData("testdata/sum_three_terms.smt2"),
			s.StringIndent(0),
			"expected strings to match",
		)
	})
}

func TestLessThanOrEqual(t *testing.T) {
	s := LessThanOrEqual{
		Literal(1),
		Literal(2),
	}
	assert.Equal(
		t,
		readTestData("testdata/lessthanorequal.smt2"),
		s.StringIndent(0),
		"expected strings to match",
	)
}

func TestGreaterThanOrEqual(t *testing.T) {
	s := GreaterThanOrEqual{
		Literal(1),
		Literal(2),
	}
	assert.Equal(
		t,
		readTestData("testdata/greaterthanorequal.smt2"),
		s.StringIndent(0),
		"expected strings to match",
	)
}

func TestMaximize(t *testing.T) {
	s := Maximize{
		Objective: Literal(1),
	}
	assert.Equal(
		t,
		readTestData("testdata/maximize.smt2"),
		s.StringIndent(0),
		"expected strings to match",
	)
}

func TestDeclareFun(t *testing.T) {
	s := DeclareFun{
		Name: "node_A",
		Type: "Bool",
	}
	assert.Equal(
		t,
		readTestData("testdata/declarefun.smt2"),
		s.StringIndent(0),
		"expected strings to match",
	)
}

func TestAssert(t *testing.T) {
	t.Run("Literal", func(t *testing.T) {
		s := Assert{
			Expression: Literal("node_A"),
		}
		assert.Equal(
			t,
			readTestData("testdata/assert.smt2"),
			s.StringIndent(0),
			"expected strings to match",
		)
	})

	t.Run("Expression_1", func(t *testing.T) {
		s := Assert{
			Expression: And{
				Left:  Literal("node_A"),
				Right: Literal("node_B"),
			},
		}
		assert.Equal(
			t,
			readTestData("testdata/assert_expression.smt2"),
			s.StringIndent(0),
			"expected strings to match",
		)
	})

	t.Run("Expression_2", func(t *testing.T) {
		s := Assert{
			Expression: Sum([]Expression{
				Ite{
					Condition: Literal("node_A"),
					TrueExpr:  Literal(1),
					FalseExpr: Literal(0),
				},
				Ite{
					Condition: Literal("node_B"),
					TrueExpr:  Literal(1),
					FalseExpr: Literal(0),
				},
			}),
		}
		assert.Equal(
			t,
			readTestData("testdata/assert_expression2.smt2"),
			s.StringIndent(0),
			"expected strings to match",
		)
	})
}

func TestGetValue(t *testing.T) {
	s := GetValue{
		Expression: Literal("node_A"),
	}
	assert.Equal(
		t,
		readTestData("testdata/getvalue.smt2"),
		s.StringIndent(0),
		"expected strings to match",
	)
}
