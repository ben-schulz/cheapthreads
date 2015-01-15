--
-- this is ~/cheapthreads/CTC/CT-1.0/CT/Factored.hs
--
-- a factoring of the top-level CT expression syntax so as to
-- remove left-recursion
--
-- put here 2010.01.04
--
-- Schulz
--

module CT.Factored where

import CT.Syntax


--
-- factored grammar redux:
--

--
-- factored expression syntax;
--
-- expressions are factored into tiers, arranged by
-- precedence of the operators.  It is assumed that
-- the parser handles these precedences correctly,
-- and so they are not made express in the grammar
--

data Expr = Top TopExpr         -- a top-level precedence expression
          | UP Expr             -- wrapper for a higher-precedence expression
          | PR POp Expr         -- prefix operator application
          | NA NonOp Expr Expr  -- non-associative infix application
          | RA RExpr            -- right-associative expression chain
          | LA LExpr            -- left-associative expression chain

instance Show Expr where
  show (Top t)      = '(':(show t) ++ ")"
  show (UP e)       = '(':(show e) ++ ")"
  show (NA op e e') = (show e) ++ ' ':(show op) ++ ' ':(show e')
  show (RA r)       = show r
  show (LA l)       = show l
  show (PR op e)    = (show op ) ++ '(':(show e) ++ ")"


instance ToCTExpr Expr where
  toCTExpr (Top t)      = toCTExpr t
  toCTExpr (UP e)       = toCTExpr e
  toCTExpr (NA op e e') = CTPrim2ary (toCTPrimOp op)
                            (toCTExpr e) (toCTExpr e')
  toCTExpr (RA e)       = toCTExpr e
  toCTExpr (LA e)       = toCTExpr e
  toCTExpr (PR op e)    = CTPrim1ary (toCTPrimOp op) (toCTExpr e)



--
-- chained right-associative expressions:
--
data RExpr = RChain Expr RExprRHS    -- chain of right-associative infixes
           | RRMost Expr             -- right-most expression in a chain

instance Show RExpr where
  show (RChain e r) = (show e) ++ ' ':(show r)
  show (RRMost e)   = (show e)


instance ToCTExpr RExpr where
  toCTExpr (RChain e (RXRHS op e')) = CTPrim2ary (toCTPrimOp op)
                                       (toCTExpr e) (toCTExpr e')


data RExprRHS = RXRHS RHOp Expr

instance Show RExprRHS where
  show (RXRHS op e) = (show op) ++ ' ':(show e)


--
-- chained left-associative expressions,
-- represented as right-recursive here for
-- the purposes of parsing:
--
data LExpr = LChain Expr LExprRHS   -- chain of left-associative infixes
           | LRMost Expr            -- right-most expression in a chain

instance Show LExpr where
  show (LChain e r) = (show e) ++ ' ':(show r)
  show (LRMost e)   = show e


instance ToCTExpr LExpr where
  toCTExpr (LChain e (LXRHS NullBind e')) = CTNullBind
                                              (toCTExpr e) (toCTExpr e')

  toCTExpr (LChain e (LXRHS Bind e')) = CTBind
                                          (toCTExpr e) (toCTExpr e')

  toCTExpr (LChain e (LXRHS op e')) = CTPrim2ary (toCTPrimOp op)
                                        (toCTExpr e) (toCTExpr e')

  toCTExpr (LRMost e) = toCTExpr e




data LExprRHS = LXRHS LHOp Expr

instance Show LExprRHS where
  show (LXRHS op e) = (show op) ++ ' ':(show e)



--
-- highest precedence expressions:
--
data TopExpr = LAM String Expr            -- lambda expression
             | FIX Expr                   -- fixed-point
             | LOOP_R Expr                -- resumptive loop
             | LOOP_RE Expr               -- reactive loop
             | ITE Expr Expr Expr         -- if-then-else
             | LET                        -- let-binding
             | CASE Expr [(CTPat, Expr)]  -- case expression
             | APP FExpr                  -- function application or atom

instance Show TopExpr where
  show (LAM x e)    = "\\" ++ x ++ " ->\n" ++ (show e)
  show (FIX e)      = "fix\n" ++ '(':(show e) ++ ")"
  show (LOOP_R e)   = "loop_R\n" ++ '(':(show e) ++ ")"
  show (LOOP_RE e)  = "loop_Re\n" ++ '(':(show e) ++ ")"
  show (ITE b e e') = "if " ++ (show b) ++
                      "\nthen" ++ (show e) ++
                      "\nelse" ++ (show e')

  show (CASE e as) = "case " ++ (show e) ++ " of\n" ++
                       (foldr (\(p, e') -> \s ->
                                         (show p) ++ " -> " ++ (show e')
                                         ++ "\n" ++ s)
                       "" as)

  show (APP f)      = show f


instance ToCTExpr TopExpr where
  toCTExpr (LAM x e)    = CTLam x (toCTExpr e)
  toCTExpr (FIX e)      = CTFix (toCTExpr e)
  toCTExpr (LOOP_R e)   = CTLoopRes (toCTExpr e)
  toCTExpr (LOOP_RE e)  = CTLoopReact (toCTExpr e)
  toCTExpr (ITE b e e') = CTBranch
                            (CTGuard $ toCTExpr b) (toCTExpr e) (toCTExpr e')

  toCTExpr (CASE e as)  = CTCase (toCTExpr e)
                            (map (\(p, e) -> (p, toCTExpr e)) as)

  -- applications are examined for special functions:
  toCTExpr (APP f) =
    case f of

      -- special function of one argument:
      (AP ((LMost (Var f')), arg))  -> case f' of
                                        "return"  -> CTReturn (toCTExpr arg)
                                        "step_R"  -> CTStepRes (toCTExpr arg)
                                        "resume_R" -> CTResumeR (toCTExpr arg)
                                        "step_Re" -> CTStepReact (toCTExpr arg)
                                        "getreq"  -> CTGetReq (toCTExpr arg)

                                        "signal" -> CTSignal
                                                       (toCTExpr arg)

                                        "get"     -> CTGet (toIdent arg)

                                        "break"   -> CTBreak (toCTExpr arg)

                                        "pop"     -> CTPop (toIdent arg)


                                        -- plus a special case for Bill:
                                        _        -> if (take 4 f') == "put_"
                                                     then
                                                       CTPut (drop 4 f')
                                                             (toCTExpr arg)
                                                     else
                                                       toCTExpr f

      -- special function of two arguments:
      (AP (AP ((LMost (Var f')), arg), arg'))  -> case f' of
                                                  "put"   -> CTPut
                                                                (toIdent arg)
                                                                (toCTExpr arg')

                                                  -- reactive-resume takes a
                                                  -- rsp as its second arg:
                                                  "resume_Re" -> CTResumeRe
                                                                 (toCTExpr arg)
                                                                 (toCTExpr arg')

                                                  "push"  -> CTPush
                                                                (toIdent arg)
                                                                (toCTExpr arg')

                                                  -- infer this to be a mem-get:
                                                  "get"   -> CTRead
                                                               (toIdent arg)
                                                               (mkindex arg')

                                                  _       -> toCTExpr f
      -- special function of three arguments;
      -- memory writes will initially parse this way,
      -- as will the bit-slice primitive:
      --
      (AP (AP (AP ((LMost (Var f')), arg), arg'), arg'')) -> case f' of
                                                              "put" ->
                                                                CTWrite
                                                                (toIdent arg)
                                                                (mkindex arg')
                                                                (toCTExpr arg'')

                                                              "slice" ->
                                                                CTPrim3ary
                                                                (Tri CTBitSlice)
                                                                (toCTExpr arg)
                                                                (toCTExpr arg')
                                                                (toCTExpr arg'')
 
                                                              _  -> toCTExpr f


      -- otherwise, it's just a normal function application:
      _                                -> toCTExpr f


--
-- produce a (possibly empty) function application:
--
data FExpr = AP (FExpr, AExpr)
           | LMost AExpr

instance Show FExpr where
  show (AP (f, a)) = '(':(show f) ++ ' ':(show a) ++ ")"
  show (LMost a)   = show a

instance ToCTExpr FExpr where

  toCTExpr (AP (f, a)) =
     case (toCTExpr f) of
       (CTCon c as)         -> CTCon c (as ++ [toCTExpr a])
       (CTApp f as)         -> CTApp (CTApp f as) (toCTExpr a)
       (CTVar f)            -> CTApp (CTVar f) (toCTExpr a)
       (CTFix e)            -> CTApp (CTFix e) (toCTExpr a)

       -- this last line allows strange usages like
       -- the appearance of bind-constructed monadic terms
       -- in the argument to a constructor:
       -- (and actually overlaps with cases above):
       --
       -- (2010.05.31) Schulz
       --
       f'                   -> CTApp f' (toCTExpr a)

  toCTExpr (LMost a) = toCTExpr a



--
-- an effectively atomic expression:
--
data AExpr = Var String     -- variable
           | Lit Literal    -- literal
           | Con String     -- constructor
           | Pair Expr Expr -- cartesian product
           | List [Expr]    -- explicit list expression
           | XNest Expr     -- parenthesized expression

instance Show AExpr where
  show (Var v)     = v
  show (Lit n)     = show n
  show (Con s)     = s
  show (Pair e e') = '(':(show e) ++ " , " ++ (show e') ++ ")"
  show (List es)   = '[':(foldr (\x -> \s -> (show x) ++ ',':s) "" es) ++ "]"
  show (XNest e)   = '(':(show e) ++ ")"

instance ToCTExpr AExpr where

  toCTExpr (Var v)       = if (take 4 v) == "get_"  -- special case for Bill
                           then CTGet (drop 4 v)
                           else CTVar v

  toCTExpr (Lit l)     =   toCTExpr l
  toCTExpr (Con c)     =   CTCon c []
  toCTExpr (Pair e e') =   CTPair (toCTExpr e) (toCTExpr e')
  toCTExpr (List es)   =   CTList (map toCTExpr es)
  toCTExpr (XNest e)   =   toCTExpr e

--
-- ... or just unwrap the identifier
--
toIdent :: AExpr -> String
toIdent (Var v) = v
toIdent (Con v) = v
toIdent x       = error $ (show x) ++ " is not an identifier!"

--
-- special case for interpreting a bracket-expression,
-- in context, as an array subscript:
--
mkindex :: AExpr -> CTExpr
mkindex (List [i]) = toCTExpr i
mkindex x          = error $ "there's a problem in your parse-job for" ++
                             " array subscripts, particularly:\n" ++
                             (show x)




--
-- primitive operations;
--
-- the precedence, fixity, and associativity of these are defined
-- in the 'OpTable' module and handled by the parser
--


--
-- left-associatives:
--
data LHOp = Mul     -- multiplication
          | Div     -- division
          | Plus    -- addition
          | Minus   -- subtraction
          | Neg     -- arithmetic negation
          | Not     -- logical negation

          -- monadic connectives:
          | Bind
          | NullBind

          -- cartesian projections:
          | FST
          | SND

          -- bit fiddling:
          | SLICE   -- bit slicing
          | BitCat  -- bitwise concatenation

instance Show LHOp where
  show Mul      = "*"
  show Div      = "/"
  show Plus     = "+"
  show Minus    = "-"
  show Bind     = ">>="
  show NullBind = ">>"
  show Neg      = "-"
  show Not      = "not"
  show FST      = "fst"
  show SND      = "snd"
  show SLICE    = "slice"
  show BitCat   = "&"


strToLHOp :: String -> LHOp
strToLHOp "*"     = Mul
strToLHOp "/"     = Div
strToLHOp "+"     = Plus
strToLHOp "-"     = Minus
strToLHOp ">>"    = NullBind
strToLHOp ">>="   = Bind
strToLHOp "not"   = Not
strToLHOp "fst"   = FST
strToLHOp "snd"   = SND
strToLHOp "slice" = SLICE
strToLHOp "&"     = BitCat

instance ToCTPrimOp LHOp where
  toCTPrimOp Mul    = Bin CTMult
  toCTPrimOp Div    = Bin CTIDiv
  toCTPrimOp Plus   = Bin CTPlus
  toCTPrimOp Minus  = Bin CTMinus
  toCTPrimOp Neg    = Un CTNeg
  toCTPrimOp Not    = Un CTNot
  toCTPrimOp FST    = Un Fst
  toCTPrimOp SND    = Un Snd
  toCTPrimOp BitCat = Bin CTBitCat

--
-- right-associatives:
--
data RHOp = Cons    -- list cons
          | Expn    -- exponentiation

          -- logical connectives:
          | AND
          | OR

instance Show RHOp where
  show Cons = ":"
  show Expn = "^"
  show AND  = "&&"
  show OR   = "||"

strToRHOp :: String -> RHOp
strToRHOp ":"  = Cons
strToRHOp "^"  = Expn
strToRHOp "&&" = AND
strToRHOp "||" = OR


instance ToCTPrimOp RHOp where
  toCTPrimOp Cons = Bin CTCons
  toCTPrimOp Expn = Bin CTExpn
  toCTPrimOp AND  = Bin CTAnd
  toCTPrimOp OR   = Bin CTOr


--
-- non-associatives:
--
data NonOp = EqTest        -- equality
           | IneqTest      -- inequality
           | LTTest        -- less than
           | GTTest        -- greater than
           | LTETest       -- less-or-equal
           | GTETest       -- greater-or-equal

instance Show NonOp where
  show EqTest   = "=="
  show IneqTest = "/="
  show LTTest   = "<"
  show GTTest   = ">"
  show LTETest  = "<="
  show GTETest  = ">="


strToNonOp :: String -> NonOp
strToNonOp "==" = EqTest
strToNonOp "/=" = IneqTest
strToNonOp "<"  = LTTest
strToNonOp ">"  = GTTest
strToNonOp "<=" = LTETest
strToNonOp ">=" = GTETest

instance ToCTPrimOp NonOp where
  toCTPrimOp EqTest   = Bin CTEqTest
  toCTPrimOp IneqTest = Bin CTIneqTest
  toCTPrimOp LTTest   = Bin CTLTTest
  toCTPrimOp GTTest   = Bin CTGTTest
  toCTPrimOp LTETest  = Bin CTLTETest
  toCTPrimOp GTETest  = Bin CTGTETest


--
-- catch-all type encompassing all primitive operations:
--
data POp = POL LHOp
         | POR RHOp
         | PON NonOp

instance Show POp where
  show (POL op) = show op
  show (POR op) = show op
  show (PON op) = show op

instance ToCTPrimOp POp where
  toCTPrimOp (POL op) = toCTPrimOp op
  toCTPrimOp (POR op) = toCTPrimOp op
  toCTPrimOp (PON op) = toCTPrimOp op



-- THIS IS THE END OF THE FILE --
