package smtlib

import (
	"bufio"
	"bytes"
	"fmt"
	"io"
	"strings"
)

// Comment represents a comment in SMT-LIB
type Comment struct {
	Text string
}

func (c Comment) String() string {
	return fmt.Sprintf("; %s", c.Text)
}

// Variable is a boolean variable in SMT-LIB
type Variable struct {
	Name string
}

func (v Variable) String() string {
	return v.Name
}

// DeclareConst represents the declare-const statement in SMT-LIB
type DeclareConst struct {
	Name string
	Type string
}

func (dc DeclareConst) String() string {
	return fmt.Sprintf("(declare-const %s %s)", dc.Name, dc.Type)
}

// SetLogic represents the set-logic statement in SMT-LIB
type SetLogic struct {
	Logic string
}

func (sl SetLogic) String() string {
	return fmt.Sprintf("(set-logic %s)", sl.Logic)
}

// SetOption represents the set-option statement in SMT-LIB
type SetOption struct {
	Key   string
	Value string
}

func (so SetOption) String() string {
	return fmt.Sprintf("(set-option :%s %s)", so.Key, so.Value)
}

// Expression is a general interface for SMT-LIB expressions
type Expression interface {
	String() string
}

// And represents a logical AND operation
type And struct {
	Left  Expression
	Right Expression
}

func (a And) String() string {
	return fmt.Sprintf("(and %s %s)", a.Left.String(), a.Right.String())
}

// Or represents a logical OR operation
type Or struct {
	Left  Expression
	Right Expression
}

func (o Or) String() string {
	return fmt.Sprintf("(or %s %s)", o.Left.String(), o.Right.String())
}

// Not represents a logical NOT operation
type Not struct {
	Operand Expression
}

func (n Not) String() string {
	return fmt.Sprintf("(not %s)", n.Operand.String())
}

// Implies represents a logical implication (=>)
type Implies struct {
	Antecedent Expression
	Consequent Expression
}

func (i Implies) String() string {
	return fmt.Sprintf("(=> %s %s)", i.Antecedent.String(), i.Consequent.String())
}

// Ite represents an if-then-else expression
type Ite struct {
	Condition Expression
	TrueExpr  Expression
	FalseExpr Expression
}

func (i Ite) String() string {
	return fmt.Sprintf("(ite %s %s %s)", i.Condition.String(), i.TrueExpr.String(), i.FalseExpr.String())
}

// Sum represents a sum of expressions
type Sum []Expression

func (s Sum) String() string {
	terms := []string{}
	for _, term := range s {
		if term == nil {
			continue
		}
		terms = append(terms, "\n  "+term.String())
	}
	return fmt.Sprintf("(+ %s)", strings.Join(terms, " "))
}

// LessThanOrEqual represents the <= expression
type LessThanOrEqual [2]Expression

func (lte LessThanOrEqual) String() string {
	terms := []string{}
	for _, term := range lte {
		if term == nil {
			continue
		}
		terms = append(terms, "\n  "+term.String())
	}
	return fmt.Sprintf("(<= %s)", strings.Join(terms, " "))
}

// GreaterThanOrEqual represents the <= expression
type GreaterThanOrEqual [2]Expression

func (gte GreaterThanOrEqual) String() string {
	terms := []string{}
	for _, term := range gte {
		if term == nil {
			continue
		}
		terms = append(terms, "\n  "+term.String())
	}
	return fmt.Sprintf("(>= %s)", strings.Join(terms, " "))
}

// Maximize represents the maximize objective
type Maximize struct {
	Objective Expression
}

func (m *Maximize) String() string {
	return fmt.Sprintf("(maximize %s)", m.Objective.String())
}

// DeclareFun represents the declare-fun statement in SMT-LIB
type DeclareFun struct {
	Name string
	Type string
}

func (df *DeclareFun) String() string {
	return fmt.Sprintf("(declare-fun %s () %s)", df.Name, df.Type)
}

// Assert represents an assert statement in SMT-LIB
type Assert struct {
	Expression Expression
}

func (a *Assert) String() string {
	return fmt.Sprintf("(assert %s)", a.Expression.String())
}

// CheckSat represents the check-sat statement in SMT-LIB
type CheckSat struct{}

func (cs *CheckSat) String() string {
	return "(check-sat)"
}

// GetModel represents the get-model statement in SMT-LIB
type GetModel struct{}

func (gm *GetModel) String() string {
	return "(get-model)"
}

// GetValue represents the get-value statement in SMT-LIB
type GetValue struct {
	Expression Expression
}

func (gv GetValue) String() string {
	return fmt.Sprintf("(get-value %s)", gv.Expression.String())
}

// Exit represents the exit statement in SMT-LIB
type Exit struct{}

func (e *Exit) String() string {
	return "(exit)"
}

// Problem represents a simple solver that can handle SMT-LIB generation
type Problem []Expression

func (p *Problem) Add(expr Expression) {
	*p = append(*p, expr)
}

// WriteTo writes the problem in S-expression form to an io.Writer
func (p Problem) WriteTo(w io.Writer) (int64, error) {
	bytes := bufio.NewWriter(w)
	var total int64

	for _, expr := range p {
		if expr == nil {
			continue
		}
		n, err := bytes.WriteString(expr.String() + "\n")
		if err != nil {
			return int64(n), err
		}
		total += int64(n)
	}

	return total, bytes.Flush()
}

// String returns the problem in S-expression form as a string
func (p Problem) String() string {
	var buf bytes.Buffer
	p.WriteTo(&buf)
	return buf.String()
}
