--
-- this is ~/cheapthreads/CTC/CT-1.0/CT/Syntax.hs
--
-- An abstract syntax for CT based on the original DSLWC'09 paper, with
-- extensions as their need has become apparent
--
-- put here 2009.12.30
--
-- Schulz
--

module CT.Syntax where

import CT.Debug
import CT.PPT

--
-- the lower-level syntax should always convert to this one:
--
class ToCTExpr a where
  toCTExpr :: a -> CTExpr

class ToCTPrimOp a where
  toCTPrimOp :: a -> CTPrimOp


--           --
-- TOP-LEVEL --
--           --

type CTIdent = String


--
-- the top-level production:
--
newtype CTProg = CTProg ([TySig], [FunDec], [DataDec], [TypeDec], [MonadDec])
                 deriving Show

instance PPT CTProg where
  ppt (CTProg (a, b, c, d, e)) =
    (foldr (\s -> \ss -> (ppt s) ++ '\n':ss) "" e) ++
    '\n':'\n':(foldr (\s -> \ss -> (ppt s) ++ '\n':ss) "" c) ++
    '\n':'\n':(foldr (\s -> \ss -> (ppt s) ++ '\n':ss) "" d) ++
    '\n':'\n':(foldr (\s -> \ss -> (ppt s) ++ '\n':ss) "" a) ++
    '\n':'\n':(foldr (\s -> \ss -> (ppt s) ++ '\n':ss) "" b) ++ "\n\n"


--
-- sift a program into list of declarations
-- of like kind:
--
siftdecs :: [CTDec] -> ([TySig], [FunDec], [DataDec], [TypeDec], [MonadDec])
siftdecs ds =

  foldr
    (\d -> \(sigs, defs, dats, syms, mons) ->

      case d of
        (CTTySig t)    -> (t:sigs, defs, dats, syms, mons)

        (CTFunDec f)   -> (sigs, f:defs, dats, syms, mons)

        (CTDataDec s)  -> (sigs, defs, s:dats, syms, mons)

        (CTTypeDec y)  -> (sigs, defs, dats, y:syms, mons)

        (CTMonadDec m) -> (sigs, defs, dats, syms, m:mons)

    ) ([], [], [], [], []) ds


--
-- check for the presence of a 'signal' declaration whenever
-- a 'ReactT' is used in a monad dec, and fill in the arguments
-- of the 'ReactT' production accordingly
-- 

bindsigs :: CTProg -> CTProg
bindsigs p@(CTProg (sigs, decs, dats, syms, mons)) = 

  let isreact  = \x -> case x of
                         (CTReactT _ _ _ _) -> True
                         _                  -> False

      issigdec = \x -> case x of
                         (SigDec _ _) -> True
                         _            -> False

      res      = filter isreact mons
      mons''   = filter (not . isreact) mons
      rqs      = filter issigdec dats
      mkq      = \xs -> (map fst xs)
      mkr      = \xs -> (map snd xs)

      lkp   = \k -> \xs -> case xs of
                             (y:ys) -> if (dnameof y) == k then y
                                       else lkp k ys

                             []     -> error $ "signal " ++ k ++ 
                                               " has no associated " ++
                                               "declaration\n\n"


  in

    case (res, rqs) of

      -- fill in request-response types:
      ((r:rs), (q:qs)) -> let mons' = foldr
                                      (\x -> \xs ->

                                        let u     = sigof x


                                            mat   = lkp u (q:qs)
                                            re    = mnameof x
                                            st    = mbelow x
                                        in
                                          (CTReactT re 
                                             (CTReqTy u (mkq $ comsigsof mat))
                                             (CTRspTy u (mkr $ comsigsof mat))
                                             st
                                          ):xs
                                

                                      )  [] (r:rs)

                          in  
                            CTProg (sigs, decs, dats, syms, mons' ++ mons'')

      -- if no ReactT instances, nothing to fill in:
      ([ ], _)         -> p

      (_, _)           -> p

--
-- possibly phasing out use of the special 'signal' declaration;
--
-- don't want this error right now
--
-- (2010.09.21) Schulz
--
{-
      -- if no signals declared, error:
      (_, [ ])         -> error $ "error: use of 'ReactT' requires " ++
                                  "declaration of at least one signal\n\n"
-}




--
-- the declarations comprising a program:
--

data CTDec = CTTySig TySig
           | CTFunDec FunDec
           | CTDataDec DataDec
           | CTTypeDec TypeDec
           | CTMonadDec MonadDec
           deriving Show

instance PPT CTDec where
  ppt (CTFunDec f)   = (ppt f) ++ "\n"
  ppt (CTTySig t)    = (ppt t) ++ "\n"
  ppt (CTMonadDec m) = (ppt m) ++ "\n"
  ppt (CTDataDec d)  = (ppt d) ++ "\n"
  ppt (CTTypeDec d)  = (ppt d) ++ "\n"



--        --
-- MONADS --
--        --

--
-- monad layer declaration:
--
--
-- only StateT layers arbitrarily;
-- ResT may only be applied to the layered state monad;
-- ReacT is similar to ResT, but with declared 'Req' and 'Rsp' types
--
-- note that 'StateT' encompasses both the ordinary one-shot StateT
-- and also the its aggregate variant, 'MemT'
--
data MonadDec = CTStateT CTIdent [(StateLT, (CTIdent, CTTy))]
              | CTResT CTIdent CTIdent
              | CTReactT CTIdent CTTy CTTy CTIdent
              deriving Show


data StateLT = StateL
             | MemL Int
             | StackL Int
             deriving Show

instance PPT MonadDec where
  ppt (CTStateT k ms) = "monad " ++ k ++  " =\n" ++
                         ( init $ init $
                         (foldr (\(l, (x, t)) -> \ss ->
                                 (ppt l) ++ '(':(ppt t) ++ ")" ++
                                 ' ':x ++ " +\n" ++ ss) "" ms))

  ppt (CTResT x y)           = "monad " ++ x ++ " = ResT " ++ y
  ppt (CTReactT x req rsp y) = "monad " ++ x ++ " = ReactT " ++
                                  (ppt req) ++ ' ':(ppt rsp) ++ ' ':y


instance PPT StateLT where
  ppt StateL     = "StateT"
  ppt (MemL n)   = "MemT " ++ (show n)
  ppt (StackL n) = "StackT " ++ (show n)


mbelow :: MonadDec -> CTIdent
mbelow (CTResT _ x)       = x
mbelow (CTReactT _ _ _ x) = x

mnameof :: MonadDec -> CTIdent
mnameof (CTStateT x _)     = x
mnameof (CTResT x _)       = x
mnameof (CTReactT x _ _ _) = x

reqof :: MonadDec -> CTTy
reqof (CTReactT _ q _ _) = q

rspof :: MonadDec -> CTTy
rspof (CTReactT _ _ r _) = r


sigof :: MonadDec -> CTIdent
sigof (CTReactT _ (CTReqTy x _) (CTRspTy y _) _) =
   if x == y then x
   else error "Bug in the parser!\n\n"


--       --
-- TYPES --
--       --

--
-- type signature:
--
data TySig = TySig CTIdent CTTy deriving Show

instance PPT TySig where
  ppt (TySig f t) = f ++ " :: " ++ (ppt t)

--
-- type constructor:
--
data TyCon = TyCon String deriving Show

instance PPT TyCon where
  ppt (TyCon s) = s

instance Eq TyCon where
  (TyCon s) == (TyCon s')  = s == s'

--
-- well-formed types:
--
data CTTy =
          -- base types:
            CTIntTy              -- "Int"
          | CTBoolTy             -- "Bool"
          | CTCharTy             -- "Char"
          | CTStringTy           -- "String"
          | CTUnitTy             -- "()"
          | CTTyVar String       -- type variable

          -- constructed types:
          | CTAbsTy CTTy CTTy    -- "type -> type"
          | CTConTy TyCon [CTTy] -- (non-monadic) constructed type

          -- more specialized constructed types:
          | CTListTy CTTy        -- list type, as a special case
          | CTMTy MTy CTTy       -- monadic type
          | CTPairTy CTTy CTTy   -- product type

          -- reactive request-response types:
          --
          -- first arg: identifier in the 'signal' declaration;
          -- second arg: keylist, where each element consists of:
          --   + a signal name
          --   + types for the actual signal data
          --
          | CTReqTy CTIdent [(CTIdent, [CTTy])]  -- reactive reqs
          | CTRspTy CTIdent [(CTIdent, [CTTy])]  -- reactive rsps

          deriving Show


data MTy = ResTy             -- resumption functor
         | ReactTy CTTy CTTy -- reactive resumption functor
         | StateTy           -- state functor
         | MVar String       -- variable functor
         deriving Show



instance PPT CTTy where
  ppt CTIntTy          = "Int"
  ppt CTBoolTy         = "Bool"
  ppt CTCharTy         = "Char"
  ppt CTStringTy       = "String"
  ppt CTUnitTy         = "()"
  ppt (CTTyVar v)      = v
  ppt (CTAbsTy t t')   = (ppt t) ++ " -> " ++ (ppt t')
  ppt (CTConTy c ts)   = (ppt c) ++ ' ':
                            (foldr (\s -> \ss -> (ppt s) ++ ' ':ss) "" ts)

  ppt (CTMTy m t)      = (ppt m) ++ ' ':(ppt t)
  ppt (CTPairTy t t')  = '(':(ppt t) ++ ',':(ppt t') ++ ")"
  ppt (CTListTy t)     = '[':(ppt t) ++ "]"

  ppt (CTReqTy _ _)   = "Req"
  ppt (CTRspTy _ _)   = "Rsp"

instance PPT MTy where
  ppt ResTy              = "R"
  ppt (ReactTy req rsp)  = "Re" ++ ' ':(ppt req) ++ ' ':(ppt rsp)
  ppt StateTy            = "K"
  ppt (MVar m)           = m

--
-- notions of type equivalence used for type inference;
--
-- note that types need not be equal according to
-- this declaration in order to unify
--
--
instance Eq CTTy where
  CTIntTy        == CTIntTy          = True
  CTBoolTy       == CTBoolTy         = True
  CTCharTy       == CTCharTy         = True
  CTStringTy     == CTStringTy       = True
  CTUnitTy       == CTUnitTy         = True
  (CTTyVar u)    == (CTTyVar v)      = u == v
  (CTAbsTy a b)  == (CTAbsTy a' b')  = (a == a') && (b == b')
  (CTPairTy u v) == (CTPairTy u' v') = (u == u') && (v == v')
  (CTConTy c ts) == (CTConTy c' ts') = (c == c) && (ts == ts')
  (CTReqTy q ts) == (CTReqTy q' ts') = (q == q') && (ts == ts')
  (CTRspTy r ts) == (CTRspTy r' ts') = (r == r') && (ts == ts')
  _              == _                = False

instance Eq MTy where
  ResTy          == ResTy           = True
  (ReactTy r q)  == (ReactTy r' q') = (r == r') && (q == q')
  StateTy        == StateTy         = True
  (MVar m)       == (MVar m')       = m == m'
  _              == _               = False


--
-- data declarations, which may be parameterized:
--

data DataDec = DataDec TyCon [CTIdent] [(TyCon, [CTTy])]

             -- the 'signal' declaration is really just a special case
             | SigDec TyCon [CommSig]
             deriving Show


-- signals are simply request-response pairs:
type CommSig = ((CTIdent, [CTTy]), (CTIdent, [CTTy]))

comsigsof :: DataDec -> [CommSig]
comsigsof (SigDec _ cs) = cs

dnameof :: DataDec -> CTIdent
dnameof (DataDec (TyCon c) _ _) = c
dnameof (SigDec (TyCon c) _)    = c


instance PPT DataDec where
  ppt (DataDec (TyCon c) ps cs) = "data " ++ c ++

    (foldr (\x -> \s -> x ++ ' ':s) "" ps) ++

    " =\n" ++
    (init $ init $
    (foldr
      (\((TyCon con), ts) -> \ss ->

        con ++ ' ':
        (foldr (\t -> \tss -> t ++ ' ':tss) "" (map ppt ts)) ++ "|\n" ++ ss
      )

      ""
      cs
    ))

  ppt (SigDec (TyCon c) ss) =
    let pfs = foldr (\x -> \s -> (ppt x) ++ ' ':s) ""
    in
      "signal " ++ c ++

      " =\n" ++
      (init $ init $
      (foldr
        (\((con, ts), (con', ts')) -> \ss ->

          '(':con ++ ' ':
          (pfs ts) ++
          ',':' ':con' ++
          ' ':(pfs ts') ++
          ")\n|" ++ ss
        )

        ""
        ss
      ))


--
-- type synonym declarations:
--
data TypeDec = TypeDec TyCon CTTy deriving Show

instance PPT TypeDec where
  ppt (TypeDec c t) = "type " ++ (ppt c) ++ " = " ++ (ppt t)



--                           --
-- FUNCTIONS AND EXPRESSIONS --
--                           --

--
-- the function declaration form:
--
--   function_identifier [parameter_identifier]* expr
--

data FunDec = FunDec CTIdent [CTIdent] CTExpr deriving Show

instance PPT FunDec where
  ppt (FunDec f ps e) = f ++
                         ' ':(foldr (\s -> \ss -> s ++ (' ':ss)) "" ps) ++
                         ' ':'=':'\n':(ppt e)

notMain :: FunDec -> Bool
notMain (FunDec "main" _ _) = False
notMain _ = True

--
-- this is just a handy helper function
-- to put 'main' at the head of the
-- function declaration list
--
promote_main :: [FunDec] -> [FunDec]
promote_main fs =

  let (m, fers) = foldr
                    (\d -> \(ms, ds) ->
                      if notMain d
                      then (ms, (d:ds))
                      else (d:ms, ds)
                    ) ([],[]) fs
      
  in
    case m of
      [m]   -> (m:fers)
      (_:_) -> error "conflicting definitions of \'main\'\n\n"
      []    -> error "no \'main\' function declared\n\n"

--
-- well-formed expressions:
--
--

data CTExpr = CTApp CTExpr CTExpr                 -- generic application
            | CTLam CTIdent CTExpr                -- lambda abstraction

            -- the standard monadic operators:
            | CTBind CTExpr CTExpr                 -- bind in any monad
            | CTNullBind CTExpr CTExpr             -- null-bind in any monad
            | CTReturn CTExpr                      -- return in any monad

            -- the stateful operators:
            | CTGet CTIdent                        -- 'get' at the state layer
            | CTPut CTIdent CTExpr                 -- 'put' at the state layer

            | CTRead CTIdent CTExpr                -- component-wise mem 'get'
            | CTWrite CTIdent CTExpr CTExpr        -- component-wise mem 'put'

            | CTPop CTIdent                        -- stack pop
            | CTPush CTIdent CTExpr                -- stack push

            -- the resumptive operators:
            | CTStepRes CTExpr                     -- resumptive 'step'
            | CTResumeR CTExpr                     -- resumption deconstruction
            | CTLoopRes CTExpr                     -- tail-recursive loop
            | CTFix CTExpr                         -- resumptive fixpoint

            -- the reactive-resumptive operators:
            | CTStepReact CTExpr                   -- resumptive 'step'
            | CTResumeRe CTExpr CTExpr             -- reactive deconstruction
            | CTLoopReact CTExpr                   -- resumptive 'step'
            | CTSignal CTExpr                      -- reactive 'signal'
            | CTGetReq CTExpr                      -- signal unpacking

            -- primitive operations:
            | CTPrim1ary CTPrimOp  CTExpr              -- unary primitives
            | CTPrim2ary CTPrimOp CTExpr CTExpr        -- binary primitives
            | CTPrim3ary CTPrimOp CTExpr CTExpr CTExpr -- tennary primitives


            -- control flow:
            | CTBranch CTGuard CTExpr CTExpr       -- 'if-then-else'
            | CTCase CTExpr [(CTPat, CTExpr)]      -- case expression
            | CTBreak CTExpr                       -- break with return val

            -- tuples:
            | CTPair CTExpr CTExpr                 -- cartesian product

            -- lists:
            | CTList [CTExpr]                      -- list expression

            -- constructed values:
            | CTCon CTIdent [CTExpr]               -- constructor and args

            -- identifiers:
            | CTVar CTIdent                        -- lexically local parameter

            -- literals:
            | CTLit Literal                        -- literals
            | CTUnit                               -- the single member of ()
            deriving Show


instance PPT CTExpr where

  ppt (CTApp f e)  = let mkfs = \a -> case a of
                                        (CTApp a a') -> (mkfs a) ++ [a']
                                        a            -> [a]
                         fs   = (mkfs f) ++ [e]
                     in
                       '(':(foldr (\x -> \s -> (ppt x) ++ ' ':s) ")" fs)

  ppt (CTLam x e)  = "(\\" ++ x ++ " ->\n" ++ (ppt e) ++ ")"

  ppt (CTBind e (CTLam x e'))    = (ppt e) ++ " >>= \\" ++ x ++ " ->\n"
                                   ++ (ppt e')

  ppt (CTNullBind e e') = (ppt e) ++ " >>\n" ++ (ppt e')
  ppt (CTReturn e)      = "return (" ++ (ppt e) ++ ")"

  ppt (CTGet x)    = "get " ++ x
  ppt (CTPut x e)  = "put " ++ x ++ " (" ++ (ppt e) ++ ")"

  ppt (CTRead x i)    = "get " ++ x ++ '[':(ppt i) ++ "]"
  ppt (CTWrite x i e) = "put " ++ x ++ '[':(ppt i) ++ "] " ++ (ppt e)

  ppt (CTPop x)       = "pop " ++ x
  ppt (CTPush x e)    = "push " ++ x ++ (ppt e)

  ppt (CTStepRes e)    = "step_R(" ++ (ppt e) ++ ")"
  ppt (CTResumeR e)    = "resume_R(" ++ (ppt e) ++ ")"
  ppt (CTLoopRes e)    = "loop_R " ++ '(':(ppt e) ++ ")"

  ppt (CTBreak e)      = "break " ++ (ppt e)

  ppt (CTFix lam) = "(fix \n" ++ '(':(ppt lam) ++ "))"

  ppt (CTStepReact e)   = "step_Re(" ++ (ppt e) ++ ")"
  ppt (CTResumeRe e e') = "resume_Re(" ++ (ppt e) ++ (ppt e') ++ ")"
  ppt (CTLoopReact e)   = "loop_Re " ++ '(':(ppt e) ++ ")"
  ppt (CTSignal e)      = "signal " ++ (ppt e)
  ppt (CTGetReq e)      = "getreq " ++ (ppt e)

  ppt (CTPrim1ary op e)        = ('(':(ppt op)) ++ "(" ++ (ppt e) ++ "))"
  ppt (CTPrim2ary op e e')     = (ppt e) ++ ' ':(ppt op) ++ ' ':(ppt e')

  ppt (CTPrim3ary op e e' e'') = ('(':(ppt op))
                                 ++ "(" ++ (ppt e) ++ ")"
                                 ++ "(" ++ (ppt e') ++ ")"
                                 ++ "(" ++ (ppt e'') ++ "))"

  ppt (CTBranch b e e') = "if " ++ (ppt b) ++ "\nthen " ++ (ppt e) ++
                          "\nelse " ++ (ppt e')

  ppt (CTCase e as) = "case " ++ '(':(ppt e) ++ ") of\n" ++
                       (foldr (\(p, e) -> \s -> '\t':(ppt p) ++ " -> "
                                                ++ (ppt e)
                                                ++ ('\n':s)) "" as)

  ppt (CTPair e e') = '(':(ppt e) ++ " , " ++ (ppt e') ++ ")"

  ppt (CTList es)   = '[':(foldr (\x -> \s -> (ppt x) ++ ',':s) "" es) ++ "]"

  ppt (CTLit l)     = ppt l

  ppt (CTVar v)     = v
  ppt (CTCon c vs)  = '(':c ++ ' ':(foldr (\x -> \s -> (ppt x) ++ ' ':s) ")" vs)
  ppt (CTUnit)      = "()"


--
-- guarding expressions:
--
-- note that, although these are normal expressions, we distinguish
-- them for ease in constraining their use further down in the compiler
--

data CTGuard = CTGuard CTExpr deriving Show

instance PPT CTGuard where
  ppt (CTGuard b) = ppt b


--          --
-- PATTERNS --
--          --

--
-- we include type annotations at this level because
-- it was expedient to do so here; however, they don't
-- contain any meaningful information until after passing
-- through the type checker
--
-- 2010.04.13 Schulz
--

data CTPat = PLit Literal CTTy         -- pattern literal
           | PVar String CTTy          -- pattern variable
           | PTuple CTPat CTPat CTTy   -- tuple pattern
           | PList [CTPat] CTTy        -- list pattern
           | PCon CTIdent [CTPat] CTTy -- constructor pattern
           | PPause CTPat CTTy         -- distinguished resumptive 'Pause'
           | PDone CTPat CTTy          -- distinguished resumptive 'Done'
           | PPauseRe CTPat CTTy         -- distinguished resumptive 'Pause'
           | PDoneRe CTPat CTTy          -- distinguished resumptive 'Done'
           | PCons CTPat CTPat CTTy    -- special 'cons' constructed pattern
           | PNest CTPat CTTy          -- nested pattern
           | Wildcard CTTy             -- always-match pattern
           deriving Show

instance PPT CTPat where
  ppt (PLit l _)      = ppt l
  ppt (PVar v _)      = v
  ppt (PTuple p p' _) = '(':(ppt p) ++ " , " ++ (ppt p') ++ ")"
  
  ppt (PList [] _)    = "[]"
  ppt (PList ps _)    = '[':
                        (tail (foldr (\x -> \s -> ',':(ppt x) ++ s) "" ps))
                        ++ "]"

  ppt (PCon c ps _)   = c ++ (foldr (\x -> \s -> ' ':(ppt x) ++ s) "" ps)
  ppt (PPause p _)    = "Pause " ++ (ppt p)
  ppt (PDone p _)     = "Done " ++ (ppt p)
  ppt (PPauseRe p _)  = "P " ++ (ppt p)
  ppt (PDoneRe p _)   = "D " ++ (ppt p)
  ppt (PCons p p' _)  = (ppt p) ++ ':':(ppt p')
  ppt (PNest p _)     = '(':(ppt p) ++ ")"
  ppt (Wildcard _)    = "_"
                         

typeofpat :: CTPat -> CTTy
typeofpat (PLit _ t)      = t
typeofpat (PVar _ t)      = t
typeofpat (PTuple _ _ t)  = t
typeofpat (PList _ t)     = t
typeofpat (PCon _ _ t)    = t
typeofpat (PPause _ t)    = t
typeofpat (PDone _ t)     = t
typeofpat (PCons _ _ t)   = t
typeofpat (PNest _ t)     = t
typeofpat (Wildcard t)    = t


--            --
-- PRIMITIVES --
--            --

--
-- catch-all primitive op type:
--
data CTPrimOp = Un CTPrimUnOp
              | Bin CTPrimBinOp 
              | Tri CTPrimTernOp deriving Show

instance PPT CTPrimOp where
  ppt (Un op)  = ppt op
  ppt (Bin op) = ppt op
  ppt (Tri op) = ppt op


--
-- primitive ternary operations:
--
data CTPrimTernOp = CTBitSlice  -- bit slicing
                    deriving Show

instance PPT CTPrimTernOp where
  ppt CTBitSlice = "slice"

--
-- primitive binary operations:
--

data CTPrimBinOp = CTCons     -- list cons

                 | CTPlus     -- addition
                 | CTMinus    -- subtraction 
                 | CTMult     -- multiplication
                 | CTIDiv     -- integer division
                 | CTExpn     -- exponentiation

                 -- boolean connectives:
                 | CTAnd      -- logical conjunction
                 | CTOr       -- logical disjunction

                 -- equality tests:
                 | CTEqTest   -- equality 
                 | CTIneqTest -- inequality 
                 | CTLTTest   -- less than 
                 | CTGTTest   -- greater than
                 | CTLTETest  -- less-or-equal
                 | CTGTETest  -- greater-or-equal

                 -- bit fiddling:
                 | CTBitCat  -- bit-wise concatenation

                 deriving Show


instance PPT CTPrimBinOp where
  ppt CTCons     = ":"
  ppt CTPlus     = "+"
  ppt CTMinus    = "-"
  ppt CTMult     = "*"
  ppt CTIDiv     = "/"
  ppt CTExpn     = "^"
  ppt CTEqTest   = "=="
  ppt CTIneqTest = "/="
  ppt CTLTTest   = "<"
  ppt CTGTTest   = ">"
  ppt CTLTETest  = "<="
  ppt CTGTETest  = ">="
  ppt CTAnd      = "AND"
  ppt CTOr       = "OR"
  ppt CTBitCat   = "&"

--
-- primitive unary operations:
--

data CTPrimUnOp = CTNeg   -- arithmetic negation
                | CTNot   -- logical negation
                | Fst     -- cartsian projection 1
                | Snd     -- cartsian projection 1
                deriving Show

instance PPT CTPrimUnOp where
  ppt CTNeg = "-"
  ppt CTNot = "not"
  ppt Fst   = "fst"
  ppt Snd   = "snd"


--
-- generic literals:
--
data Literal = LitInt Int       -- integer literal
             | LitBool Bool     -- boolean literal
             | LitChar Char     -- character literal
             | LitString String -- string literal
             | UnitEl           -- the unit element
             deriving Show

instance PPT Literal where
  ppt (LitInt n)    = show n
  ppt (LitBool b)   = show b
  ppt (LitChar c)   = [c]
  ppt (LitString s) = show s
  ppt UnitEl        = "()"

instance ToCTExpr Literal where
  toCTExpr UnitEl      = CTUnit
  toCTExpr l           = CTLit l

instance Eq Literal where
  (LitInt n)     ==  (LitInt m)    =  m == n
  (LitBool n)    ==  (LitBool m)   =  m == n
  (LitChar n)    ==  (LitChar m)   =  m == n
  (LitString n)  ==  (LitString m) =  m == n
  UnitEl         ==  UnitEl        = True
  _              ==  _             = False
  x              /=  y             = not (x == y)


-- THIS IS THE END OF THE FILE --
