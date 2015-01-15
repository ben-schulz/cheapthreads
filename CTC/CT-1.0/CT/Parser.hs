--
-- this is ~/cheapthreads/CTC/CT-1.0/CT/Parser.hs
--
-- the cleaned-up CT parser (and lexer)
--
-- put here 2010.01.02
--
-- Schulz
--

module CT.Parser where


import CT.Syntax
import CT.Factored
import CT.OpTable

import Data.Char
import Text.ParserCombinators.Parsec

import CT.Debug




--           --
-- TOP-LEVEL --
--           --

ctprog :: Parser CTProg
ctprog =
  spaces >>
  (endBy ctdec (spaces <|> eof)) >>= \ds ->
  return $ bindsigs $ CTProg $ siftdecs ds
  

ctdec :: Parser CTDec
ctdec =

  try
  (
    monaddec

    <|>
    datadec

    <|>
    typedec

    <|>
    try tysig

    <|>
    try fundec
  ) >>= \d ->
  return d


--               --
-- BASIC PARSERS --
--               --

symbol :: String -> Parser String
symbol s = spaces >> (string s) >> space >> spaces >> return s

--
-- strip all the comments out of the input string:
--
clean_input :: Parser String
clean_input = manyTill (comment <|> anyChar) eof
  


--
-- parse past a Haskell-style comment:
--
-- we replace the comment with an approrpiate
-- number of  '\n's, so as
-- not to screw up the line numbers.
--
-- however, this doesn't currently preserve
-- line numbers when block comments are present
--
comment :: Parser Char
comment =
  (
    try (string "--") >>
    (manyTill anyChar (char '\n')) >>
    return '\n'
  )

  <|>
  (between (string "{-") (string "-}") (many (noneOf "}-") >> return '\n'))


--              --
-- DECLARATIONS --
--              --


--
-- monad declaration,
--
-- as:
--
--   monaddec    ::=  "monad " con "=" monaddecRHS
--   monaddecRHS ::= statet | restt | reactt
--   restt       ::= "ResT" con
--   reactt      ::= "ReacT" tycon tycon con
--   
-- note the small quirk in the 'ReacT' syntax, namely
-- that two type constructors are expected, though they
-- need not be called "Req" or "Rsp".
--
--
monaddec :: Parser CTDec
monaddec =


  -- every monaddec begins with "monad con =":
  try (keyword "monad") >>
  spaces >>
  con >>= \m -> 
  spaces >>
  (char '=') >>
  spaces >>

  -- possible transformer syntax appearing to the right:
  (
    -- state:
    try (statet >>= \ss -> (return $ CTMonadDec $ CTStateT m ss))

    <|>
    (
      (string "Re") >> (

      -- ordinary resumption:
      try
      (
        (keyword "sT") >>
        spaces >>
        con >>= \k ->
        (return $ CTMonadDec $ CTResT m k)
      )

      -- reactive resumption:
      <|>
      try
      (
        (keyword "actT") >>
        spaces >>
        tycon >>= \req ->

        spaces >>
        tycon >>= \rsp ->

        spaces >>
        con >>= \k ->
        (return $ CTMonadDec $ CTReactT m (CTConTy req []) (CTConTy rsp []) k)

        -- arg lists for requests and responses are filled in at a later stage:
--        (return $ CTMonadDec $ CTReactT m (CTReqTy q []) (CTRspTy q []) k)
      ))

    )
  )


--
-- type signature,
--
-- as:
--
--   tysig ::= var '::' ctty
--

tysig :: Parser CTDec
tysig =
  var >>= \f ->
  spaces >>
  (string "::") >>
  spaces >>
  ctty >>= \t ->
  (return $ CTTySig $ TySig f t)

--
-- data declaration,
--
-- as:
--
--   datadec ::= "data" tycon "=" tycon ctty* "|" [tycon ctty*]*
--
datadec :: Parser CTDec
datadec = (try datad) <|> sigd

datad :: Parser CTDec
datad =
  try (keyword "data") >>
  spaces >>
  tycon >>= \c ->
  spaces >>
  (many (var >>= \v -> spaces >> return v)) >>= \ps ->
  spaces >>
  (char '=') >>
  spaces >>
  condec >>= \c1 ->
  (many condecRHS) >>= \cs -> 
  (return $ CTDataDec $ DataDec c ps (c1:cs))


--
-- the top-level 'signal' declaration, which is effectively
-- just a 'data' declaration:
--
sigd :: Parser CTDec
sigd =
  try (keyword "signal") >>
  spaces >>
  tycon >>= \c ->
  spaces >>
  (char '=') >>
  spaces >>
  commpair >>= \c1 ->
  (many (try commpairRHS)) >>= \cs -> 
  (return $ CTDataDec $ SigDec c (c1:cs))


commpair :: Parser CommSig
commpair =
  spaces >>
  (char '(') >>
  spaces >>
  ((try (char '(' >> spaces)) <|> (return ())) >> -- possible parens around term
  con >>= \c ->
  spaces >>
  (many ctty) >>= \ts ->
  spaces >>
  ((try (char ')' >> spaces)) <|> (return ())) >> -- possible parens around term
  (char ',') >>
  spaces >>
  con >>= \c' ->
  spaces >>
  (many ctty) >>= \ts' ->
  spaces >>
  (char ')') >>
  return ((c, ts), (c', ts'))

commpairRHS :: Parser CommSig
commpairRHS = spaces >> (symbol "|") >> commpair
  


--
-- constructor declaration inside of a 'data' dec:
--
condec :: Parser (TyCon, [CTTy])
condec =
  tycon >>= \c ->
  spaces >>
  (many ctty) >>= \ts ->
  spaces >>
  return (c, ts)

condecRHS :: Parser (TyCon, [CTTy])
condecRHS =
  (symbol "|") >>
  condec >>= \c ->
  return c



--
-- type synonym declarations,
--
-- as:
--
--   typedec ::= "type" tycon "=" ctty
--
typedec :: Parser CTDec
typedec =
  try (keyword "type") >>
  spaces >>
  tycon >>= \s ->
  spaces >>
  (symbol "=") >>
  spaces >>
  ctty >>= \t ->
  (return $ CTTypeDec $ TypeDec s t)


--
-- function declarations,
--
-- as:
--
--   fundec ::= var var* expr
--
-- where the 'var*' is a sequence of parameters
-- separated by whitespaces
--
fundec :: Parser CTDec
fundec =
  var >>= \f ->
  spaces >>
  (many (var >>= \v -> spaces >> return v)) >>= \xs ->
  spaces >>
  (char '=') >>
  spaces >>
  ctexpr >>= \e ->
  (return $ CTFunDec $ FunDec f xs e)


--        --
-- MONADS --
--        --

--
-- state layer,
--
-- as:
--
--   statet = statelayer ["+" statelayer]*
--
statet :: Parser [(StateLT, (CTIdent, CTTy))]
statet =
  (sepBy1

     (try statelayer <|> memlayer <|> stacklayer)
     (try (spaces >> (char '+') >> spaces))

  ) >>= \ls ->

  (return ls)


statelayer :: Parser (StateLT, (CTIdent, CTTy))
statelayer =
  (string "StateT") >>
  spaces >>

  (between
     ((char '(') >> spaces)
     (spaces >> (char ')'))
      ctty
  ) >>= \t ->

  spaces >>
  con >>= \c ->
  return (StateL, (c, t))



memlayer :: Parser (StateLT, (CTIdent, CTTy))
memlayer =
  (string "MemT") >>
  spaces >>
  (many digit) >>= \n ->
  spaces >>

  (between
     ((char '(') >> spaces)
     (spaces >> (char ')'))
      ctty
  ) >>= \t ->

  spaces >>
  con >>= \c ->
  return (MemL (atoi n), (c, t))


--
-- identical to the above, except for "StackT":
--
stacklayer :: Parser (StateLT, (CTIdent, CTTy))
stacklayer =
  (string "StackT") >>
  spaces >>
  (many digit) >>= \n ->
  spaces >>

  (between
     ((char '(') >> spaces)
     (spaces >> (char ')'))
      ctty
  ) >>= \t ->

  spaces >>
  con >>= \c ->
  return (StackL (atoi n), (c, t))



--
-- resumption layer,
--
-- as:
--
--   restt ::= "monad " con "=" "ResT" con
--
restt :: Parser CTIdent
restt =
  spaces >>
  (keyword "ResT") >>
  spaces >>
  con >>= \y ->
  (return y)



--       --
-- TYPES --
--       --


--
-- type identifier,
--
-- as:
--
--   ctty  ::= tyterm | tyterm '->' ctty
--
ctty :: Parser CTTy
ctty =

  -- type must begin with one of: primitive, constructed, or "(type)"
  tyterm >>= \t ->
  spaces >>

  (
    -- chaining for function types:
    ((string "->") >>
    spaces >>
    ctty >>= \t' ->
    (return $ CTAbsTy t t'))
  
    -- otherwise, RMost reached
    <|>
    (return t)
  )



--
-- type bound more tightly than '->'
--
-- as:
--
--   tyterm ::= prim_type | tycon tyterm | (ctty)
--

tyterm :: Parser CTTy
tyterm =

  try prim_type

  <|>
  (
    tycon >>= \c -> 
    return $ CTConTy c []
  )

  -- product types:
  <|>
  try
  (
    (char '(') >>
    spaces >>
    ctty >>= \t ->
    spaces >>
    (char ',') >>
    spaces >>
    ctty >>= \t' ->
    spaces >>
    (char ')') >>
    return (CTPairTy t t')
  )

  <|>
  try
  (
    (char '(') >>
    tycon >>= \c ->
    spaces >>

    (many
       (
         tyterm >>= \y -> 
         spaces >>
         return y
       )
    ) >>= \ts ->
    (char ')') >>

    (return $ CTConTy c ts)
  )

  <|>
  try (between ((char '(') >> spaces) (spaces >> (char ')')) ctty)

  -- list types:
  <|>
  (
    (between ((char '[') >> spaces) (spaces >> (char ']')) ctty) >>= \t ->
    return $ CTListTy t
  )


--
-- primitive types,
--
-- as:
--
--   prim_type ::= Int | Bool | ()
--
prim_type :: Parser CTTy
prim_type =

  (((string "Int") >> notFollowedBy alphaNum) >> return CTIntTy)

  <|>
  (((string "Bool") >> notFollowedBy alphaNum) >> return CTBoolTy)

  <|>
  (((string "Char") >> notFollowedBy alphaNum) >> return CTCharTy)

  <|>
  (((string "String") >> notFollowedBy alphaNum) >> return CTStringTy)

  <|>
  (unitel >> return CTUnitTy)


--
-- type constructor,
--
-- as:
--
--   tycon ::= con
--
tycon :: Parser TyCon
tycon = con >>= \c -> return (TyCon c)





--             --
-- EXPRESSIONS --
--             --


--
-- top-level expression parser:
--
ctexpr :: Parser CTExpr
ctexpr = (expr 0) >>= \e -> (return $ toCTExpr e)

--
-- a refactoring of the grammar in module CT.Syntax;
--
-- this grammar is based on the expression grammar in the
-- Haskell 98 report; it is converted into the expression
-- grammar in CT.Syntax using the 'ToCTExpr' typeclass
--
-- 2010.11.01 Schulz
--

expr :: Int -> Parser Expr

-- by convention, 10 is the highest precedence level;
-- all applications of 'expr' should eventually reach this one

expr 10 =

  -- lambda:
  try
  (
    (char '\\') >>
    spaces >>
    var >>= \x ->
    (symbol "->") >>
    expr 0 >>= \e ->
    (return $ Top $ LAM x e)
  )


  -- resumptive loops:
  <|>
  try
  (
    (keyword "loop_R") >>
    spaces >>
    expr 0 >>= \e ->
    (return $ Top $ LOOP_R e)
  )

  <|>
  try
  (
    (keyword "loop_Re") >>
    spaces >>
    expr 0 >>= \e ->
    (return $ Top $ LOOP_RE e)
  )

  -- fix-point:
  <|>
  try
  (
    (keyword "fix") >>
    spaces >>
    expr 0 >>= \e ->
    (return $ Top $ FIX e)
  )

  -- conditional expression:
  <|>
  try
  (
    (keyword "if") >>
    spaces >>
    (expr 0) >>= \b ->
    spaces >>
    (keyword "then") >>
    spaces >>
    (expr 0) >>= \e ->
    spaces >>
    (keyword "else") >>
    spaces >>
    (expr 0) >>= \e' ->
    (return $ Top $ ITE b e e')
  )

  -- let-expression:

  -- case-expression:
  <|>
  try
  (
    (keyword "case") >>
    spaces >>
    (expr 0) >>= \o ->
    spaces >>
    (keyword "of") >>
    many (oneOf " \t") >>
    newline >>
    (many1 (try casealt)) >>= \as ->  -- note that we do NOT require the '\n'
    (return $ Top $ CASE o as)
  )

  -- otherwise, look for a function application:
  <|>
  try
  (
    aexpr >>= \a ->
    (
      try
      (
        -- try for a sequence of arguments:
        many (oneOf "\t ") >>
        (many1 $
          try
          (
            aexpr >>= \a ->

              -- I'm not happy with this change
              -- (from 'spaces' to 'oneOf "\t "'),
              -- but we currently
              -- need it in order to allow function headers
              -- to include variables; otherwise, they will
              -- be read as function applications
              --
              -- the cost is that function application cannot span
              -- lines, which displeases me
              --
              -- 2010.02.03 Schulz

            many (oneOf "\t ") >>


            -- disambiguate a variable in an application
            -- from a variable heading a declaration,
            -- or a case alternative:
            notFollowedBy
            (
              (char '=')
 
              <|>
              try (char ':' >> char ':')

              <|>
              try (char '-' >> char '>')

            ) >>
            return a
         )
        ) >>= \as -> 
        (return $ Top $ APP $ lassoc (LMost a) as)
      )

      -- if no arguments, it's just an atom
      <|>
      (return $ Top $ APP $ LMost a)
    )
  )


--
-- general case: build a high-precedence expression
-- from low-precedence ones, following a bottom-up procedure
--
expr n =

  -- every expression begins with a higher-precedence
  -- expression on the left:

  (
    -- try for a possible prefix operator at this precedence:
    try 
    (
      lhop n Prefix >>= \op ->   -- this could be '-' or 'not'

      spaces >>
      expr (n + 1) >>= \e ->
      (return $ PR (POL op) e)

    )

    -- otherwise, just jump up one precedence 
    <|>
    (expr (n + 1))
  ) >>= \e ->



  -- try for an operator following:
  (

    -- non-associative:
    try
    (
      spaces >>
      (nonop n Infix) >>= \op ->
      spaces >>
      expr (n + 1) >>= \e' ->
      (return $ NA op (UP e) (UP e'))
    )
        
     
    -- right-associative:
    <|>
    try ((rexprrhs n)>>= \r -> (return $ RA $ RChain (UP e) r))

    -- left-associative:
    <|>
    try ((lexprrhs n) >>= \r -> (return $ LA $ LChain (UP e) r))

    -- otherwise, there's no operator chain
    <|>
    (return e)
  )




--
-- left-associative chaining of infix operators:
--
lexpr :: Int -> Parser LExpr
lexpr n =

  expr (n + 1) >>= \e ->

  (
    (
      lexprrhs n >>= \e' ->
      (return $ LChain (UP e) e')
    )

    <|>
    (
      return $ LRMost e
    )
  )



lexprrhs :: Int -> Parser LExprRHS
lexprrhs n =
  spaces >>
  (lhop n Infix) >>= \op ->
  spaces >>
  (expr n) >>= \e ->
  (return $ LXRHS op e)
  

   
--
-- right-associative chaining of infix operators:
--
rexpr :: Int -> Parser RExpr
rexpr n =

  expr (n + 1) >>= \e ->

  (
    -- either expression is followed by an op and a chain
    (
      (rexprrhs n) >>= \r ->
      (return $ RChain e r)
    )

    -- or is the right-most in the chain
    <|>
    (return $ RRMost e)
  )


rexprrhs :: Int -> Parser RExprRHS
rexprrhs n =

  spaces >>
  (rhop n Infix) >>= \op ->
  spaces >>
  (expr n) >>= \e ->
  (return $ RXRHS op e)
  


--
-- parse an effectively atomic expression:
--
aexpr :: Parser AExpr
aexpr =

  -- a literal:
  try (literal >>= \x -> (return $ Lit x))

  -- or a variable:
  <|>
  try (var >>= \v -> (return $ Var v))

  -- or a constructor:
  <|>
  try (con >>= \c -> (return $ Con c))

  -- or an explicit list expression:
  <|>
  try
  (
    (char '[') >>

    spaces >>

    (
      -- which may contain expressions:
      try 
      (
        (expr 0) >>= \e ->
        spaces >>

        (
          -- more than one element:
          many1
          (
            (char ',') >>
            spaces >>
            (expr 0) >>= \e' ->
            spaces >>
            return e'
          )
       
          -- or just one element:
          <|>
          (return [])

        ) >>= \es ->

        (return (e:es))
      )

      -- or may be empty:
      <|>
      (return [])

    ) >>= \es -> 

    (char ']') >>
    return (List es)
  )

  -- or a parenthesized expression:
  <|>
  try
  (
    (char '(') >>
    spaces >>
    (expr 0) >>= \e ->
    spaces >>

    -- which may be a pair, or just nested:
    (
      -- try for the product:
      try
      (
        (char ',') >>
        spaces >>
        (expr 0) >>= \e' ->
        spaces >>
        (char ')') >>
        (return $ Pair e e')
      )

      -- otherwise, it's just nested
      <|>
      (
        (char ')') >> (return $ XNest e)
      )
    )
  )



--
-- parse an operator;
--
-- see module 'OpTable' for a full list of operators
--

--
-- parse a left-associative operator:
--
lhop :: Precedence -> CTFixity -> Parser LHOp

-- special case to disambiguate negation from subtraction:
lhop n Prefix =
  let ops = foldr (\o -> \ps ->
                    (try $ string o):ps) [] (getOps n Prefix LHAssoc)
  in
    (choice ops) >>= \s -> case s of
                             "-" -> return Neg
                             _   -> return $ strToLHOp s
  
-- general case:
lhop n f =
  let ops = foldr (\o -> \ps -> (try $ string o):ps) [] (getOps n f LHAssoc)
  in
    (choice ops) >>= \s -> (return $ strToLHOp s)


--
-- parse a right-associative operator:
--
rhop :: Precedence -> CTFixity -> Parser RHOp
rhop n f =
  let ops = foldr (\o -> \ps -> (try $ string o):ps) [] (getOps n f RHAssoc)
  in
    (choice ops) >>= \s -> (return $ strToRHOp s)


--
-- parse a non-associative operator:
--
nonop :: Precedence -> CTFixity -> Parser NonOp
nonop n f =
  let ops = foldr (\o -> \ps -> (try $ string o):ps) [] (getOps n f NonAssoc)
  in
    (choice ops) >>= \s -> (return $ strToNonOp s)



--          -- 
-- PATTERNS -- 
--          -- 

--
-- this is a very, very simple pattern parser;
--
-- Nesting of patterns is allowed, but cons will
-- only parse if the LHS is a variable, literal, or wildcard.
--

ctpat :: Parser CTPat
ctpat =
  apat >>= \p ->
  spaces >>

  (
    -- try for a cons:
    try (
      (char ':') >>
      spaces >>
      ctpat >>= \p' ->
      (return $ PCons p p' CTUnitTy)
    )


    -- otherwise, it's a simple pattern:
    <|>
    (return p)
  )



--
-- try for an atomic (non-cons) pattern:
--
apat :: Parser CTPat
apat =

  -- try for an atomic pattern:
  try
  (
    -- literal pattern:
    (literal >>= \l -> (return $ PLit l CTUnitTy))

    -- or a pattern variable:
    <|>
    (var >>= \v -> (return $ PVar v CTUnitTy))

    -- or a wildcard:
    <|>
    (char '_' >> (return $ Wildcard CTUnitTy))
  )
  
  -- otherwise, try for a general constructor:
  <|>
  try 
  (
    con >>= \c ->
    spaces >>
    many (apat >>= \a -> spaces >> return a) >>= \ps ->

    return 
      (
        -- we make special distinctions for:
        -- 'Pause', 'Done', 'P', 'D'
        case (c, ps) of

          ("P", [p])     -> PPauseRe p CTUnitTy
          ("D", [p])     -> PDoneRe p CTUnitTy
          ("Pause", [p]) -> PPause p CTUnitTy
          ("Done", [p])  -> PDone p CTUnitTy
          _              -> PCon c ps CTUnitTy
      )

  )

  -- otherwise, try for a list pattern:
  <|>
  try
  (
      (char '[') >>

    (

      -- ... which may be empty:
      try 
      (
        spaces >>
        (char ']') >>
        (return $ PList [] CTUnitTy)
      )

      -- ... or not
      <|>
      (
        ctpat >>= \p ->

        many (
          spaces >>
          (char ',') >>
          spaces >>
          ctpat
        ) >>= \ps ->

        spaces >>
        (char ']') >>
        (return $ PList (p:ps) CTUnitTy)
      )
    )
  )


  -- otherwise, try for a parenthesized pattern:
  <|>
  try
  (
    (char '(') >>
    spaces >>
    ctpat >>= \p ->
    spaces >>

    (
      -- which may be a tuple:
      try
      (
        (char ',') >>
        spaces >>
        ctpat >>= \p' ->
        spaces >>
        (char ')') >>
        (return $ PTuple p p' CTUnitTy)
      )

      -- or just a parenthesized expression
      <|>
      (
        (char ')') >>
        (return $ PNest p CTUnitTy)
      )
    )
    
  )


--
-- parse a full case alternative:
--
casealt :: Parser (CTPat, Expr)
casealt =
  spaces >>
  ctpat >>= \p ->
  spaces >>
  (string "->") >>
  spaces >>
  (expr 0) >>= \e ->
  return (p, e)



--                           --
-- CONCRETE SYNTAX DETAILS   --
--                           --


--
-- look for any operator:
--
--
anyopchar :: Parser Char
anyopchar = oneOf opchars

opchars :: [Char]
opchars = "+-*/^><=!~"



--
-- reserved keywords in the concrete syntax:
--

keyword_tokens :: [String]
keyword_tokens = [

  "if",
  "then",
  "else",
  "fix",
  "case",
  "of",
  "let",
  "in"
           ]



--                    --
-- LEAVES OF THE AST: --
--                    --

--
-- top-level literal parser:
--
literal :: Parser Literal
literal =

  -- interger literal:
  (litint >>= \n -> (return $ LitInt n))

  -- or a boolean literal:
  <|>
  (litbool >>= \b -> (return $ LitBool b))


  -- or a string literal:
  <|>
  (litstring >>= \s -> (return $ LitString s))

   -- or the unit element:
  <|>
  (
    (char '(') >>
    spaces >>
    (char ')') >>
    (return $ UnitEl)
  )



--
-- parse an integer literal
--
-- as:
--
--   litint ::= ('1..9') ('0..9')*
--
-- negative integers are handled through 
-- the expression case for prefix negation
--
litint :: Parser Int
litint =
  many1 digit >>= \ds ->
  return $ atoi ds


--
-- parse a boolean literal
--
-- as:
--
-- litbool ::= 'False' | 'True'
--
litbool :: Parser Bool
litbool =
  ((string "False") <|> (string "True")) >>= \b ->
  case b of
    "False" -> return False
    "True"  -> return True


--
-- parse a string literal;
--
-- this is an overly simplistic parser
-- put here as a stub; it (obviously) does not
-- handle escaped characters
--
litstring :: Parser String
litstring =
  (char '"') >>
  (many (noneOf ['"'])) >>= \s ->
  (char '"') >>
  return s

--
-- an identifier that is not a reserved keyword,
--
-- as:
--
--   var ::= lower ('_' | alphaNum)*
--
-- , excluding keyword strings
--
--
var :: Parser String
var =
  (keywords <|> return "") >>= \k ->
  case k of
    ""   ->  lower >>= \c ->
             (many (alphaNum <|> char '_' <|> char '\'')) >>= \cs ->
             (return (c:cs))

    _    ->  (many1 (alphaNum <|> char '_')) >>= \cs ->
             (return $ k ++ cs)


--
-- a constructor:
--
-- we assume here that we do NOT need to worry
-- about disambiguating keywords from constructors,
-- i.e. assume no keyword begins with an uppercase
--
--
con :: Parser String
con =
  upper >>= \c ->
  (many (alphaNum <|> char '_')) >>= \cs ->
  return (c:cs)



--
-- the distinguished unit element:
--
-- as:
--   unitel ::= '()'
--
unitel :: Parser Literal
unitel = (try ((char '(') >> spaces >> (char ')'))) >> return UnitEl



--
-- parse keyword:
--
keyword :: String -> Parser String
keyword s =
  (
    (string s) >> 
    (notFollowedBy (alphaNum <|> char '_'))
  ) >>
  return s


--
-- look for a reserved token:
--
keywords :: Parser String
keywords =
  let ks = foldr (\k -> \ps -> (try $ string k):ps) [] keyword_tokens
  in
    (choice ks) >>= \s -> return s



--             --
-- BOILERPLATE --
--             --

--
-- String to Int, assuming a well-formed string:
--
atoi :: String -> Int
atoi ('-':ds) = negate $ atoi ds
atoi ds = foldl (\n -> \d -> (digitToInt d) + 10 * n) 0 ds

--
-- turn a list into a left-associative structure:
--
lassoc :: FExpr -> [AExpr] -> FExpr
lassoc f [a]    = AP (f, a)
lassoc f (a:as) = lassoc (AP (f, a)) as

--
-- I don't remember putting this here.  I think someone else added it.
--
-- since the changes to the debugging output, 'ctparse' now does
-- the same thing as the code below
--
-- 2010.03.05 Schulz
--

-- this is now out of synch with the rest of the code
--
-- 2010.03.08 Schulz
{-
parseCT :: String -> IO ()
parseCT fname = do
                    input <- readFile fname
                    let parseRes = (runParser ctprog () fname input)
                    case parseRes of
                        Left _  -> (print "PARSE ERROR")
                        Right a -> (print a)
-}


-- THIS IS THE END OF THE FILE --
