--
-- this is ~/cheapthreads/ctc_working/CT-1.0/RPSLam/CPS.hs
--
-- a quick way of computing/visualizing CPS transforms;
-- mainly here so I can study CPS without having to do all these
-- by hand, which is terrible.
--
-- put here 2011.02.02
--
-- Schulz
--

module CPS where

import PPT
import Compile.RSyntax
import MonadicConstructions


type M a = StateT (Int, Int, Int) Id a

genk :: M String
genk = get >>= \(k, m, n) ->
       upd (\(k, m, n) -> (k+1, m, n)) >>
       return ("k" ++ (show k))

genm :: M String
genm = get >>= \(k, m, n) ->
       upd (\(k, m, n) -> (k, m+1, n)) >>
       return ("m" ++ (show m))

genn :: M String
genn = get >>= \(k, m, n) ->
       upd (\(k, m, n) -> (k, m, n+1)) >>
       return ("n" ++ (show n))


run_m m = (fst . deId) ((deST m) (0, 0, 0))


data CTerm = CVar String
           | CLam String CTerm
           | CApp CTerm CTerm

instance PPT CTerm where
  ppt (CVar x)    = x
  ppt (CLam x t)  = "(\\" ++ x ++ '.':(ppt t) ++ ")"
  ppt (CApp t t') = '(':(ppt t) ++ ' ':(ppt t') ++ ")"


cps :: CTExpr -> M CTerm
cps (CTVar x)    = genk >>= \k ->
                   return (CLam k (CApp (CVar k) (CVar x)))

cps (CTLam x t)  = genk >>= \k ->
                   cps t >>= \t' ->
                   return (CLam k (CApp (CVar k) (CLam x t')))

cps (CTApp t t') = genk >>= \k ->
                   genm >>= \m ->
                   genn >>= \n -> 

                   cps t >>= \s ->
                   cps t' >>= \s' ->

                   return
                     (CLam k
                       (CApp s (CLam m
                         (CApp s' (CLam n
                           (CApp (CApp (CVar m) (CVar n)) (CVar k)) )))))
                       


-- THIS IS THE END OF THE FILE --
