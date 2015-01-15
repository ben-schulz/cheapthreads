--
-- this is ~/cheapthreads/CTC/CT-1.0/RPSLam/Compile/HCompile.hs
--
-- a code generation module for the handler component of the
-- RPS demonstration compiler;
--
-- this translates a slightly modified version of the CT abstract
-- syntax augmented with 'rdEnv' and 'inEnv' primitives into a simplified
-- imperative language;
--
-- put here 2010.12.28
--
-- Schulz
--

module Compile.HCompile where

import Compile.RSyntax
import Compile.Constants
import Targets.Syntax

import MonadicConstructions


import Data.Char
import Data.List





-- a fixpoint label is bound to a list of all declared variables
-- in its scope:
type Binding = String -> ([Ref], [Ref])

initbind = \_ -> ([], [])

tweek :: (Eq a) =>(a -> b) -> a -> b -> (a -> b)
tweek f x v = \y -> if y == x then v else f y


type M a = EnvT Binding (StateT (Int, Int, Int, Int, Int) Id) a

prj_h (ENV a) = ((fst . deId) ((deST (a initbind)) (0, 0, 0, 0, 0)))


genlocal :: M Label
genlocal =

  liftEnv $
  get >>= \(n, _, _,  _, _) ->
  upd (\(n, m, o, p, q) -> (n + 1, m, o, p, q)) >>
  return ("HANDL" ++ (show n))

genbind :: M Label
genbind =
  liftEnv $
  get >>= \(_, m, _, _, _) ->
  upd (\(n, m, o, p, q) -> (n, m + 1, o, p, q)) >>
  return ("HBIND" ++ (show m))

genbrs :: M (Label, Label)
genbrs =
  liftEnv $
  get >>= \(_, _, o, _, _) ->
  upd (\(n, m, o, p, q) -> (n, m, o + 1, p, q)) >>
  let n' = show o
  in
    return ("HBRTRUE" ++ n', "HBRFALSE" ++ n')

genvar :: M String
genvar =
  liftEnv $
  get >>= \(_, _, _, p, _) ->
  upd (\(n, m, o, p, q) -> (n, m, o, p + 1, q + 1)) >>
  return ("__hvar__" ++ (show p))


getcts :: M Int
getcts =
  liftEnv $
  get >>= \(_, _, _, _, q) ->
  return q

rollbackcts :: Int -> M ()
rollbackcts c = liftEnv (upd (\(n, m, o, p, _) -> (n, m, o, p - c, 0)))


--
-- compilation of monadic actions:
--
hcompile_act :: CTExpr -> M Code

hcompile_act (CTBind r@(Resume _ _) (CTLam x r')) = 

  hcompile_act r >>= \p ->
  hcompile_act r' >>= \p' ->

  genbind >>= \l ->
  genlocal >>= \l' ->

  let x'  = Var x
      tc  = StructFld x' callfld
      tq  = StructFld x' reqfld
      td  = StructFld x' donefld
      tv  = StructFld x' valfld

      a    = Assign tc (DeRef R_Nxt)
      a'   = Assign tq (DeRef R_Req)
      a''  = Assign td (DeRef R_Done)
      a''' = Assign tv (DeRef R_Ret)
  in
    return
      (Labeled l
        (codecat p (Labeled l' (Seq a (Seq a' (Seq a'' (Seq a''' p')))))))


hcompile_act (CTBind r (CTLam x r')) = hcompile_act r >>= \p ->
                                       hcompile_act r' >>= \p' ->
                                       genlocal >>= \l ->
                                       genbind >>= \l' ->
                                       let rt = Assign (Var x) (DeRef R_Ret)
                                       in
                                         return
                                           (Labeled l
                                             (codecat p
                                               (Labeled l' (Seq rt p'))))

hcompile_act (CTNullBind r r')       = hcompile_act r >>= \p ->
                                       hcompile_act r' >>= \p' ->
                                       genlocal >>= \l ->
                                       return
                                         (Labeled l (codecat p p'))


hcompile_act (CTReturn x)            = hcompile_expr x >>= \v -> 
                                       genlocal >>= \l ->
                                       let rt = Assign R_Ret v
                                       in
                                       return 
                                         (Labeled l (Seq rt End))


hcompile_act RdEnv                   = let rt = Assign R_Ret (DeRef R_Env)
                                       in
                                         return (Seq rt End)


hcompile_act (InEnv x r)             =  hcompile_act r >>= \p ->
                                        hcompile_expr x >>= \e -> 
                                        let ps = PushEnv e
                                            re = Assign R_Env e
                                            pp = Seq PopEnv
                                                   (Seq (Assign R_Env TopEnv)
                                                     End)
                                        in
                                          return 
                                            (Seq ps (Seq re (codecat p pp)))


hcompile_act (Resume (CTVar r) v)    = hcompile_expr v >>= \u ->
                                       genlocal >>= \l ->
                                       let rp = Assign R_Rsp u
                                           jm = JSR (Var r)
                                       in
                                         return
                                           (Seq rp (Labeled l (Seq jm End)))
                                           

hcompile_act (CTBranch b r r')       = hcompile_expr b >>= \v ->
                                       hcompile_act r >>= \p ->
                                       hcompile_act r' >>= \p' ->
                                       genbrs >>= \(l, l') -> 
                                       genlocal >>= \l'' -> 
                                       let bz = BZ v l'
                                           jm = Seq (JmpI l'') End
                                           tr = Labeled l (codecat p jm)
                                           fl = Labeled l' p'
                                           en = Labeled l'' End
                                       in
                                         return
                                           (Seq bz (codecat tr (codecat fl en)))
                                         

hcompile_act (CTFix (CTLam k r))     = rdEnv >>= \rho ->

                                       -- this call:

                                       hcompile_act (lamb r) >>= \p ->

                                       -- is actually an ad hoc
                                       -- static analysis, to determine 
                                       -- any assignments that occur in the 
                                       -- body of the term;
                                       -- actual compilation pass is below:
                                       -- (2011.01.14) Schulz


                                       genlocal >>= \l ->
                                       genlocal >>= \l' ->

                                       let as   = nub (getas p)
                                           ps   = map Var (lamps r)
                                           rho' = tweek rho k (ps, as)
                                           hd   = mkpt k

                                           -- entry path to the loop:
                                           st   = Labeled l (Seq (JSRI hd) End)
                                           it   = JmpI l

                                           -- loop exit:
                                           rt   = Seq Return End

                                           ex   = Seq (JmpI l') End
                                           en   = Labeled l' End
                                       in

                                       -- undo any variable generation
                                       -- done during the tentative pass:
                                       getcts >>= \n ->
                                       rollbackcts n >>

                                       -- and perform the actual compilation:
                                       inEnv rho'
                                         (hcompile_act (lamb r)) >>= \p' ->

                                         return
                                           (codecat
                                             (codecat
                                               (Seq it (Labeled hd p')) rt)
                                             st)
                                         -- (codecat (Seq it (Labeled hd p')) st)
                                             

{-
                                       -- make frame push:
                                       let hd    = mkpt k

                                           -- pop all variables, including
                                           -- lambda parameters
                                           -- at the top of the loop;
                                           -- these are pushed elsewhere
                                           -- before the jump occurs:
                                           as    = getas p'
                                           psh   = map (Push . DeRef) as
                                           pps'  = map Pop (reverse as)

                                           pps   = foldr
                                                   (\s -> \p -> Seq s p) End
                                                     (map (Pop . Var) (lamps r))

                                       in
                                         return
                                           (Labeled hd
                                             (codecat pps'' (codecat p' rt)))
                                         
-}


hcompile_act (CTApp f@(CTFix (CTLam _ (CTLam s _))) x) =
                                               hcompile_expr x >>= \x' ->
                                               hcompile_act f >>= \f' ->
                                               let it = Assign (Var s) x'
                                               in
                                                 return (Seq it f')


-- this case only treats case of one loop variable;
-- ADD MULTIPLE PARAMETERS IN FUTURE
-- (2011.01.13) Schulz
hcompile_act (RecApp (CTVar k) x)    = rdEnv >>= \rho ->
                                       genlocal >>= \l ->
                                       hcompile_expr x >>= \v ->

                                       let (ps, vs) = rho k
                                           vs'      = ps ++ vs

                                           -- form push/pop of local variables:
                                           psh      = map (Push . DeRef) vs'
                                           pps      = map Pop (reverse vs')

                                           -- push before call, pop after
                                           psh'     = foldr
                                                      (\s -> \c -> Seq s c)
                                                        End psh

                                           pps'     = foldr
                                                      (\s -> \c -> Seq s c)
                                                        End pps
                                         
                                           -- assign the new parameter value:
                                           it       = case ps of
                                                        [p] -> Seq
                                                                 (Assign p v)
                                                                   End
                                                        []  -> End
                                                        

                                           -- make the jump
                                           js       = JSRI (mkpt k)
                                       in
                                         return
                                           (codecat psh'
                                             (codecat it (Seq js pps')))
                                           
                                             

{-
                                       let fr = Push v
                                           js = JSRI (mkpt k)
                                       in
                                         genlocal >>= \l ->
                                         return
                                           (Seq fr 
                                             (Labeled l (Seq js End)))
-}


hcompile_act (Lkp x)                 = return (Seq (LkpV x) End)


--
-- this case is identical to that for ordinary 'case' expressions,
-- except that the current state of the resumption referenced by
-- the matching expression is read before matching occurs
--
-- (2011.01.12) Schulz
--

hcompile_act (CaseStar (CTVar x) as) =

  let x' = DeRef (RR x)
  in

  genvar >>= \v ->

  (
    foldr
    (\(p, a) -> \m ->

      hcompile_act a >>= \c ->
      m >>= \cs ->
      return (c:cs)

    ) (return []) as

  ) >>= \ps ->

  let o   = Assign (Var v) x'
      bs  = map (\(p, _) -> mkmatchcond (Var v) p) as
      ss  = map (\(p, _) -> mkpatassigns (Var v) p) as
      ss' = zipWith codecat ss ps
  in
    foldbranch (zip bs ss') >>= \bz ->
    genlocal >>= \l ->
    return (Labeled l (Seq o bz))


hcompile_act (CTCase x as) =

  hcompile_expr x >>= \x' ->
  genvar >>= \v ->

  (
    foldr
    (\(p, a) -> \m ->

      hcompile_act a >>= \c ->
      m >>= \cs ->
      return (c:cs)

    ) (return []) as

  ) >>= \ps ->

  let o   = Assign (Var v) x'
      bs  = map (\(p, _) -> mkmatchcond (Var v) p) as
      ss  = map (\(p, _) -> mkpatassigns (Var v) p) as
      ss' = zipWith codecat ss ps
  in
    foldbranch (zip bs ss') >>= \bz ->
    genlocal >>= \l ->
    return (Labeled l (Seq o bz))



hcompile_act x = error $ show x



--
-- transliteration to expressible values in the target:
--
hcompile_expr :: CTExpr -> M TExpr

hcompile_expr (CTVar x)    = return (DeRef (Var x))

hcompile_expr (CTCon c vs) = (
                               foldr
                               (\v -> \m ->
                                 hcompile_expr v >>= \v' -> 
                                 m >>= \vs' ->
                                 return (v':vs')
                               )
                                 (return []) vs

                             ) >>= \vs' ->

                             let vs'' = attachl structfld vs'
                                 con  = (confld, (VX (SymConstant c)))
                             in
                               return (ConX c (con:vs''))

hcompile_expr (XEnv h x v)  = hcompile_expr h >>= \h' ->
                              hcompile_expr x >>= \x' ->
                              hcompile_expr v >>= \v' ->
                              return (TxEnv h' x' v')

hcompile_expr x = error $ show x




--
-- extensive book-keeping and setup for case expressions:
--


--
-- generate a boolean expression from a pattern match:
--
mkmatchcond :: Ref -> CTPat -> TExpr

mkmatchcond x (PNest p _) = mkmatchcond x p

mkmatchcond x (PCon c ps _) =

  -- constructor match corresponds to equality with its declared constant:
  let cm = EqTst
             (DeRef (StructFld x confld))
             (VX (SymConstant (mkcon c)))

      -- associate each subpattern to its corresponding field
      fs = attachl structfld  ps

      -- form conditions for each of the subpatterns, localized
      -- to the proper field:
      fs' = map (\(m, p) -> mkmatchcond (StructFld x m) p) fs
  in
    foldr
      (\e -> \e' -> And e e') cm fs'


-- resumption matches:
mkmatchcond x (PPauseRe (PTuple p p' _) _) =

  let dn = EqTst (VX (BolT False)) (DeRef (StructFld x donefld))
      rq = mkmatchcond (StructFld x reqfld) p
      cd = mkmatchcond (StructFld x callfld) p'
  in
    And dn (And rq cd)


mkmatchcond x (PDoneRe p _) =

  let dn = StructFld x donefld
  in
    And (EqTst (VX (BolT True)) (DeRef dn)) (mkmatchcond dn p)
    
    

mkmatchcond _ (PVar _ _)   = VX (BolT True)
mkmatchcond _ (Wildcard _) = VX (BolT True)

mkmatchcond _ x = error $ show x


mkpatassigns :: Ref -> CTPat -> Code
mkpatassigns x (PNest p _) = mkpatassigns x p

mkpatassigns x (PCon c ps _) = let fs  = attachl structfld ps

                                   fs' = map
                                           (\(l, p) ->
                                             (StructFld x l, p)) fs

                                   as = (map
                                          (\(v, p) -> mkpatassigns v p)
                                            fs')
                               in
                                 (foldr (\k -> \m -> codecat k m) End as)


mkpatassigns x (PPauseRe (PTuple p p' _) _) = let c = StructFld x callfld
                                                  q = StructFld x reqfld
                                              in
                                              foldr
                                                (\k -> \m -> codecat k m) End
                                                  [mkpatassigns q p,
                                                   mkpatassigns c p']


mkpatassigns x (PDoneRe p _) = let dn = StructFld x valfld
                               in
                                 mkpatassigns dn p

mkpatassigns x (PVar v _)    = Seq (Assign (Var v) (DeRef x)) End
mkpatassigns x (Wildcard _)  = End



patvars :: CTPat -> [String]
patvars (PNest p _)     = patvars p
patvars (PTuple p p' _) = (patvars p) ++ (patvars p')
patvars (PCon _ ps _)   = concat $ map patvars ps
patvars (PPause p _)    = patvars p
patvars (PDone p _)     = patvars p
patvars (PPauseRe p _)  = patvars p
patvars (PDoneRe p _)   = patvars p
patvars (PCons p p' _)  = (patvars p) ++ (patvars p')
patvars (PList ps _)    = concat $ map patvars ps
patvars (PVar x _)      = [x]
patvars _               = []


foldbranch :: [(TExpr, Code)] -> M Code
foldbranch as =

  genlocal >>= \l'' ->

  (
    foldr
      (\(x, p) -> \m ->

        genbrs >>= \(l, l') ->
        m >>= \b ->
        let tr = Labeled l p
            fl = Labeled l' b
            jm = Seq (JmpI l'') End
            bz = BZ x l'
        in
          return (Seq bz (codecat (codecat tr jm) fl))

      )
        (return End) as

  ) >>= \p' ->

  return (codecat p' (Labeled l'' End))


--
-- get all assigned variables within the body of a fix;
-- used to form variable pushes and pops for implementing
-- recursion;
--
getas :: Code -> [Ref]
getas (Labeled _ p) = getas p
getas (Seq (Assign (Var v) _) p)         = (Var v):(getas p)
getas (Seq (Assign (StructFld r _) _) p) = (baseref r):(getas p)
getas (Seq _ p) = getas p
getas End       = []


baseref (StructFld r _) = baseref r
baseref r = r


--
-- miscellaneous data structure handling:
--

lamps :: CTExpr -> [CTIdent]
lamps (CTLam x t) = x:(lamps t)
lamps _           = []

lamb :: CTExpr -> CTExpr
lamb (CTLam _ t) = lamb t
lamb t           = t


mkpt k = '_':'_':(map toUpper k)


--mkcon c = '_':'_':(map toUpper c)
mkcon = id





-- THIS IS THE END OF THE FILE --
