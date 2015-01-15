--
-- this is ~/cheapthreads/CTC/CT-1.0/CT/fopspec.hs
--
-- a simplified specification of the output of the front-end,
-- for use as a reference document
--
-- put here 2010.03.02
--
-- Schulz
--

{---------------------------------------------------------------------

INTRODUCTION

The CT front-end consists of three main components: (1) the parser,
(2) the type inferencer, and (3) the inliner.  At a later stage,
a variety of static checks will be added as one or more modules, although
this will not affect the structure of the output from the front-end.
The final output of the front-end consists of a syntax tree in which each
node is annotated with its corresponding type, and all function (i.e. lambda)
applications have been beta-reduced.


OPERATIONAL OVERVIEW

Control flows from the parser, to the type inferencer, to the inliner.

The parser implements a factored syntax similar to that in the Haskell 98
report.  Provided that no parse errors occur, the factored syntax is transformed
into a simplified, unfactored syntax that more closely resembles the BNF grammar
presented in the DSLWC'09 paper.  Associativities and scopes of basic operations
are determined during the transformation, and retained through the type
inference and inlining phases.

Type inference is performed on the AST output by the parser.  The type
inferencer is structured as a monadic interpreter for the abstract syntax
given in module 'Syntax'.  The interpreter crawls the syntax tree, generating
tentative annotations (containing provisional type variables), which are
applied to each respective node, and collecting the associated constraints.
After crawling the full syntax tree, a straightforward unification 
procedure is applied to the collected constraints in order to produce 
a substitution of all resolvable (i.e. not essentially ambiguous) type
variables in the annotated syntax tree.

Inlining is not strictly necessary, but simplifies later compliation phases.
The inliner applies a naive, maximally aggressive inlining procedure which
presupposes certain essential constraints of CT.  Most important among these
is the assumption that recursion occurs only via explicitly declared fixpoints.
Inlining proceeds essentially as a kind of abstract interpretation which simply
beta-reduces all terms in the AST.  The result is that 'main' becomes the root
of a single syntax tree equivalent to the original program, with all function
applications replaced according to their respective declarations.  The inliner
also makes a single change to the structure of the abstract syntax itself,
incorporating the arguments of a fixpoint application into the same production
as the fixpoint itself.  The importance of this change is that it ensures
that the only applications remaining in the final syntax tree correspond to
invocations of tail recursion inside of a 'fix' structure.


DESCRIPTION OF THE OUTPUT

The final output from the front-end is structured according to the data
structure defined in module 'INAST'.  However, the actual output of the
front-end is somewhat less general than the definition of INAST, and can
be succinctly described as the following BNF grammar:

  <program> ::= <mterm>

  <mterm>   ::= <rterm>
              | <kterm>

  <rterm>   ::= step <mterm>
              | fix (\<ident> -> (\<ident ->)* <fixb>) <pterm>*
              | if <pterm> then <rterm> else <rterm>
              | <rterm> >>= \<ident> -> <rterm>
              | <rterm> >> <rterm>
              | return <pterm>

  <fixb>    ::= <rterm>
              | tail_call

  <kterm>   ::= get <ident>
              | put <ident> <pterm>
              | if <pterm> then <kterm> else <kterm>
              | <kterm> >>= \<ident> -> <kterm>
              | <kterm> >> <kterm>
              | return <pterm>

  <pterm>   ::= <val>
              | if <pterm> then <pterm> else <pterm>
              | <pterm> <pop> <pterm>
              | <pop> <pterm>

  <val>     ::= literal
              | variable reference via an <ident>

  <pop>     ::= any of the primitive operations given in module 'OpTable'

  <ident>   ::= any legal identifier


In the actual AST output, 'tail_call' will appear as an application; in fact,
any application remaining in the final output should correspond to a tail-call
inside the scope of some fixpoint.  Note that lambdas appear only
in the context of fixpoint or a bind.  The <identifier> appearing in a
lambda may be used as a variable reference (<val>) within the scope of that
lambda.

The type inferencer should ensure that tail-calls are applied to the correct
number of arguments, and that primitive operations are applied to well-typed
values.  Note also that conditional expressions ('if-then-else') may occur at
any level of the syntax, but must be guarded by a non-monadic expression.

---------------------------------------------------------------------}
