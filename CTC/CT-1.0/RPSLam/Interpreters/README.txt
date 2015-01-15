this is ~/cheapthreads/CTC/CT-1.0/RPSLam/interpreters

put here (2010.12.11)

Schulz

A series of interpreters demonstrating the calculation of a compiler for
PCF using the resumption-passing style.

We use PCF as formulated in Gunter's "Semantics of Programming Languages",
which uses the arithmetic/control primitives as constructors rather than
as constants.

This directory includes a parser for a Haskell-like functional syntax,
and a top-level module for invoking the various interpreters for testing.



Quick start:


+ 'run_all' invokes all interpreters and shows their respective outputs.


+ For simplicity of parsing, conditional expressions require their
  sub-expressions to be parenthesized, i.e.

    if (t) then (t') else (t'')

+ Recursion is implemented using the Mu-operator, which is written as:

    u x -> t

  in the concrete syntax, i.e. "x is a recursive fixpoint in t", which
  should obey the usual operational semantics.
