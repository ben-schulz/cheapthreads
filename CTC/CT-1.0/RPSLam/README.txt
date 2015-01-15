The code in this directory contains full Haskell code for a small compiler
for the typed lambda calculus, based upon the resumption-passing transformation.

The top-level invocation is contained in './Test.hs'.

The directory "./Ex" contains a number of working examples in a simple concrete
syntax.

In module 'Test', the following functions invoke the compiler's various
features:

  'run_obj fp' parses and compiles the text file at path 'fp' and interprets
  the resulting loop code.

  (note that, for the 'ackermann' example, the interpreter may take a while
  to terminate.)

  'compile fp' parses and compiles the text file at path 'fp' and writes
  a concrete-syntax description of the result to './a.out'

The directory './Interpreters' contains running Haskell code describing
each of the definitional interpreters used in the step-wise development of the
final RPS intepreter used in the paper.

Originally compiled and run using GHC 6.12.1, using the Parsec
parser-combinatory package.

-- Benjamin Schulz (2010.12)
