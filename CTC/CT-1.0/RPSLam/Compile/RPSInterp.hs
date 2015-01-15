--
-- this is ~/cheapthreads/CTC/CT-1.0/RPSLam/Compile/RPSInterp.hs
--
-- transformation of a term in the PCF abstract syntax (in PCF.Syntax)
-- into a term in the simplified reactive-resumption term syntax
-- (defined in Compile.Syntax, i.e. './Syntax') according to the
-- interpreter semantics in Interpreters.InterpRe
--
-- succinctly: take the reactive term in Interpreters.InterpRe and
-- put it into an abstract syntax representing the monadic term produced
-- by Interpreters.InterpRe.interp
--
-- put here (2010.12.14)
--
-- Schulz
--

module Compile.RPSInterp where

import PCF.Syntax
import Compile.ReSyntax

import MonadicConstructions

type M a = StateT Int Id a

genvar :: M Name
genvar = get >>= \n -> 
         upd (+1) >>
         return ("x" ++ (show n))



--                --
-- TOP-LEVEL CALL -- 
--                --

rps :: Term -> TermRe
rps t = (fst . deId) ((deST (rps_transform t)) 0)

--                     --
-- MAIN TRANSFORMATION --
--                     --


rps_transform :: Term -> M TermRe


rps_transform (Lam x t)     = rps_transform t >>= \r ->
                              return (Signal (MkCl x r))

rps_transform (App t t')    = genvar >>= \x ->
                              genvar >>= \x' -> 
                              rps_transform t >>= \r ->
                              rps_transform t' >>= \r' ->
                              let sig = (Signal (Apply (Ref x) (Ref x')))
                              in
                                -- return (Bind x r (Bind x' r' sig))
                                 return (Bind x' r' (Bind x r sig))
                              

rps_transform (Inc t)       = genvar >>= \x -> 
                              rps_transform t >>= \r ->
                              let q   = IsNum (Ref x)
                                  r'  = Eta (IncX (Ref x)) 
                                  r'' = Eta (Lit Wrong)
                                  ite = ITE q r' r''
                              in
                                return (Bind x r ite)

rps_transform (Dec t)       = genvar >>= \x -> 
                              rps_transform t >>= \r ->
                              let q   = IsNum (Ref x)
                                  r'  = Eta (DecX (Ref x)) 
                                  r'' = Eta (Lit Wrong)
                                  ite = ITE q r' r''
                              in
                                return (Bind x r ite)

rps_transform (ZTest t)     = genvar >>= \x -> 
                              rps_transform t >>= \r ->
                              let q    = EqTest (Ref x) (Lit (Num 0))
                                  q'   = IsNum (Ref x)
                                  r'   = Eta (Lit (Bol True))
                                  r''  = Eta (Lit (Bol False))
                                  r''' = Eta (Lit Wrong)
                                  ite  = ITE q r' (ITE q' r'' r''')
                              in
                                return (Bind x r ite)
                                

rps_transform (EF t t' t'') = genvar >>= \x -> 
                              rps_transform t >>= \r ->
                              rps_transform t' >>= \r' ->
                              rps_transform t'' >>= \r'' ->
                              --let q   = EqTest (Ref x) (Lit (Bol False))
                              let q   = (Ref x)
                                  q'  = IsBool (Ref x)
                                  ite = ITE q r' (ITE q' r'' (Eta (Lit Wrong)))
                              in
                                return (Bind x r ite)

rps_transform (Mu x t) = rps_transform t >>= \r ->
                         return (Signal (MkRecCl x r))

rps_transform (Var x)  = return (Signal (Lkp x))
rps_transform (Con n)  = return (Eta (Lit (Num n)))
rps_transform (Bit b)  = return (Eta (Lit (Bol b)))




-- THIS IS THE END OF THE FILE --
