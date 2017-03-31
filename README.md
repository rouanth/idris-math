# idris-ratio-calc

A calculator for rational numbers written in Idris.

Unfortunately, it only works in Idris' REPL and we've been unable yet to
diagnole the problem.

This project is an exam work for the Computer Science Club's course on Idris
programming.

## Usage

Load `main.idr` into the REPL with `idris main.idr`. Then run `run` with the
string that you wish evaluated:

```idris
    run "1; 2; f(x, y) = (15 * x) / (16 * y); f(1, 2); f = 5; f"
```

A list of results shall be output after a while.

## Language

Statements are separated by a semicolon.

A statement can be a plain expression, which is then evaluated, with its result
put into the list that `run` shall return, or an assignment, which are
distinguished by having `=` in them. Assignments shall start with an identifier,
then an optional list of parameters in brackets can follow, then the `=` occurs,
and then an expression is expected.

Expressions can include `+`, `-`, `*`, and `/` operations. The precedence is the
obvious one. One can override the precedence with brackets. Operands can be
constants and identifiers, with identifiers optionally accepting a
comma-separated list of parameters in brackets.

Failure isn't supported. If one provides an identifier with the wrong number of
parameters, it's evaluated as zero. Failing to parse a program results in an
empty list.
