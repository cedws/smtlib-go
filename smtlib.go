package smtlib

import (
	"bufio"
	"bytes"
	"fmt"
	"io"
	"strings"
)

var (
	_ Expression = literal{}
	_ Expression = Comment{}
	_ Expression = DeclareConst{}
	_ Expression = SetLogic{}
	_ Expression = SetOption{}
	_ Expression = And{}
	_ Expression = Or{}
	_ Expression = Not{}
	_ Expression = Implies{}
	_ Expression = Ite{}
	_ Expression = Sum{}
	_ Expression = LessThan{}
	_ Expression = GreaterThan{}
	_ Expression = LessThanOrEqual{}
	_ Expression = GreaterThanOrEqual{}
	_ Expression = Maximize{}
	_ Expression = DeclareFun{}
	_ Expression = Assert{}
	_ Expression = CheckSat{}
	_ Expression = GetModel{}
	_ Expression = GetValue{}
	_ Expression = Exit{}
	_ Expression = Push{}
	_ Expression = Pop{}
)

func indent(s string, n int) string {
	indent := strings.Repeat(" ", n)
	return indent + s
}

func maybeIndent(e Expression, n int) string {
	if _, ok := e.(literal); ok {
		return e.String()
	}
	return e.StringIndent(n)
}

// Expression is a general interface for SMT-LIB expressions
type Expression interface {
	StringIndent(int) string
	String() string
}

type literal struct{ any }

// Literal is a literal value in SMT-LIB
func Literal(v any) Expression {
	return literal{v}
}

func (l literal) StringIndent(n int) string {
	return indent(fmt.Sprintf("%v", l.any), n)
}

func (l literal) String() string {
	return l.StringIndent(0)
}

// Comment represents a comment in SMT-LIB
type Comment struct {
	Text string
}

func (c Comment) StringIndent(n int) string {
	return indent(fmt.Sprintf("; %s", c.Text), n)
}

func (c Comment) String() string {
	return c.StringIndent(0)
}

// DeclareConst represents the declare-const statement in SMT-LIB
type DeclareConst struct {
	Name string
	Type string
}

func (dc DeclareConst) StringIndent(n int) string {
	return indent(fmt.Sprintf(
		"(declare-const %s %s)",
		dc.Name,
		dc.Type,
	), n)
}

func (dc DeclareConst) String() string {
	return dc.StringIndent(0)
}

// SetLogic represents the set-logic statement in SMT-LIB
type SetLogic struct {
	Logic string
}

func (sl SetLogic) StringIndent(n int) string {
	return indent(fmt.Sprintf(
		"(set-logic %s)",
		sl.Logic,
	), n)
}

func (sl SetLogic) String() string {
	return sl.StringIndent(0)
}

// SetOption represents the set-option statement in SMT-LIB
type SetOption struct {
	Key   string
	Value string
}

func (so SetOption) StringIndent(n int) string {
	return indent(fmt.Sprintf(
		"(set-option :%s %s)",
		so.Key,
		so.Value,
	), n)
}

func (so SetOption) String() string {
	return so.StringIndent(0)
}

// And represents a logical AND operation
type And struct {
	Left  Expression
	Right Expression
}

func (a And) StringIndent(n int) string {
	return indent(fmt.Sprintf(
		"(and %s %s)",
		maybeIndent(a.Left, n),
		maybeIndent(a.Right, n+2),
	), n)
}

func (a And) String() string {
	return a.StringIndent(0)
}

// Or represents a logical OR operation
type Or struct {
	Left  Expression
	Right Expression
}

func (o Or) StringIndent(n int) string {
	return indent(fmt.Sprintf(
		"(or %s %s)",
		maybeIndent(o.Left, n+2),
		maybeIndent(o.Right, n+2),
	), n)
}

func (o Or) String() string {
	return o.StringIndent(0)
}

// Not represents a logical NOT operation
type Not struct {
	Operand Expression
}

func (no Not) StringIndent(n int) string {
	return indent(fmt.Sprintf(
		"(not %s)",
		maybeIndent(no.Operand, n+2),
	), n)
}

func (no Not) String() string {
	return no.StringIndent(0)
}

// Implies represents a logical implication (=>)
type Implies struct {
	Antecedent Expression
	Consequent Expression
}

func (i Implies) StringIndent(n int) string {
	return indent(fmt.Sprintf(
		"(=> %s %s)",
		maybeIndent(i.Antecedent, n+2),
		maybeIndent(i.Consequent, n+2),
	), n)
}

func (i Implies) String() string {
	return i.StringIndent(0)
}

// Ite represents an if-then-else expression
type Ite struct {
	Condition Expression
	TrueExpr  Expression
	FalseExpr Expression
}

func (i Ite) StringIndent(n int) string {
	return indent(fmt.Sprintf(
		"(ite %s %s %s)",
		maybeIndent(i.Condition, n+2),
		maybeIndent(i.TrueExpr, n+2),
		maybeIndent(i.FalseExpr, n+2),
	), n)
}

func (i Ite) String() string {
	return i.StringIndent(0)
}

// Sum represents a sum of expressions
type Sum []Expression

func (s Sum) StringIndent(n int) string {
	var terms []string

	if len(s) == 0 || s[0] == nil {
		return "(+)"
	}

	terms = append(terms, maybeIndent(s[0], 0))

	for _, term := range s[1:] {
		if term == nil {
			continue
		}
		terms = append(terms, maybeIndent(term, n+2))
	}

	join := "\n" + strings.Repeat(" ", n)

	return indent(fmt.Sprintf(
		"(+ %s)",
		strings.Join(terms, join),
	), n)
}

func (s Sum) String() string {
	return s.StringIndent(0)
}

// LessThan represents the < expression
type LessThan [2]Expression

func (lt LessThan) StringIndent(n int) string {
	var terms []string

	terms = append(terms, lt[0].String())
	terms = append(terms, lt[1].String())

	join := " "
	return indent(fmt.Sprintf(
		"(< %s)",
		strings.Join(terms, join),
	), n)
}

func (lt LessThan) String() string {
	return lt.StringIndent(0)
}

// GreaterThan represents the > expression
type GreaterThan [2]Expression

func (gt GreaterThan) StringIndent(n int) string {
	var terms []string

	terms = append(terms, gt[0].String())
	terms = append(terms, gt[1].String())

	join := " "
	return indent(fmt.Sprintf(
		"(> %s)",
		strings.Join(terms, join),
	), n)
}

func (gt GreaterThan) String() string {
	return gt.StringIndent(0)
}

// LessThanOrEqual represents the <= expression
type LessThanOrEqual [2]Expression

func (lte LessThanOrEqual) StringIndent(n int) string {
	var terms []string

	terms = append(terms, lte[0].String())
	terms = append(terms, lte[1].String())

	join := " "
	return indent(fmt.Sprintf(
		"(<= %s)",
		strings.Join(terms, join),
	), n)
}

func (lte LessThanOrEqual) String() string {
	return lte.StringIndent(0)
}

// GreaterThanOrEqual represents the >= expression
type GreaterThanOrEqual [2]Expression

func (gte GreaterThanOrEqual) StringIndent(n int) string {
	var terms []string

	terms = append(terms, gte[0].String())
	terms = append(terms, gte[1].String())

	join := " "
	return indent(fmt.Sprintf(
		"(>= %s)",
		strings.Join(terms, join),
	), n)
}

func (gte GreaterThanOrEqual) String() string {
	return gte.StringIndent(0)
}

// Maximize represents the maximize objective
type Maximize struct {
	Objective Expression
}

func (m Maximize) StringIndent(n int) string {
	return indent(fmt.Sprintf(
		"(maximize %s)",
		maybeIndent(m.Objective, n+2),
	), n)
}

func (m Maximize) String() string {
	return m.StringIndent(0)
}

// DeclareFun represents the declare-fun statement in SMT-LIB
type DeclareFun struct {
	Name string
	Sort string
	Type string
}

func (df DeclareFun) StringIndent(n int) string {
	return indent(fmt.Sprintf(
		"(declare-fun %s (%s) %s)",
		df.Name,
		df.Sort,
		df.Type,
	), n)
}

func (df DeclareFun) String() string {
	return df.StringIndent(0)
}

// Assert represents an assert statement in SMT-LIB
type Assert struct {
	Expression Expression
}

func (a Assert) StringIndent(n int) string {
	return indent(fmt.Sprintf(
		"(assert %s)",
		maybeIndent(a.Expression, 0),
	), n)
}

func (a Assert) String() string {
	return a.StringIndent(0)
}

// CheckSat represents the check-sat statement in SMT-LIB
type CheckSat struct{}

func (cs CheckSat) StringIndent(n int) string {
	return indent("(check-sat)", n)
}

func (cs CheckSat) String() string {
	return cs.StringIndent(0)
}

// GetModel represents the get-model statement in SMT-LIB
type GetModel struct{}

func (gm GetModel) StringIndent(n int) string {
	return indent("(get-model)", n)
}

func (gm GetModel) String() string {
	return gm.StringIndent(0)
}

// GetValue represents the get-value statement in SMT-LIB
type GetValue struct {
	Expression Expression
}

func (gv GetValue) StringIndent(n int) string {
	return indent(fmt.Sprintf(
		"(get-value %s)",
		maybeIndent(gv.Expression, n+2),
	), n)
}

func (gv GetValue) String() string {
	return gv.StringIndent(0)
}

// Exit represents the exit statement in SMT-LIB
type Exit struct{}

func (e Exit) StringIndent(n int) string {
	return indent("(exit)", n)
}

func (e Exit) String() string {
	return e.StringIndent(0)
}

// Push represents the push statement in SMT-LIB
type Push struct{}

func (p Push) StringIndent(n int) string {
	return indent("(push)", n)
}

func (p Push) String() string {
	return p.StringIndent(0)
}

// Pop represents the pop statement in SMT-LIB
type Pop struct{}

func (p Pop) StringIndent(n int) string {
	return indent("(pop)", n)
}

func (p Pop) String() string {
	return p.StringIndent(0)
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
		total += int64(n)

		if err != nil {
			return total, err
		}
	}

	return total, bytes.Flush()
}

// String returns the problem in S-expression form as a string
func (p Problem) String() string {
	var buf bytes.Buffer
	p.WriteTo(&buf)
	return buf.String()
}
