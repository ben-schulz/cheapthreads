{-# LANGUAGE FunctionalDependencies,MultiParamTypeClasses,TypeSynonymInstances #-}
module Defunctionalizer where

import Prelude hiding (pi)
import MonadicConstructions
import CommonTypes
import DefunMonad
import MonadicBoilerplate
import Assorted
import Syntax
import Parser
import IO
import System.IO.Unsafe 


----------------------------------------
--           Some Examples            --
----------------------------------------

mkstart k i = Rule ((VLab k,In,init0),(ILab $ i+1,Out,init0))

defun :: MExp -> IO ()
defun e = case e of
               (Fix k _ _) -> putStrLn "\ninitial_state = state_k" >>
                              (mapM_ rule2FSM $ run (defunR e))
               _           -> putStrLn ("\ninitial_state = state_" ++ show init_label) >>
                              (mapM_ rule2FSM $ run (defunR e))

rules :: MExp -> IO ()
rules e = case e of
               (Fix k _ _) -> putStrLn ("\ninitial_state = " ++ k) >>
                              (pretty $ run (defunR e))
               _           -> putStrLn ("\ninitial_state = state_" ++ show init_label) >>
                              (pretty $ run (defunR e))

rule :: MExp -> IO ()
rule e = putStrLn (show $ mkrule (defunK e))


mktrans lhs rhs i      = [Rule((ILab i,In,lhs),(ILab $ i+1,Out,rhs))]
mkrectrans lhs rhs k i = [Rule((ILab i,In,lhs),(VLab k,Out,rhs))]

--
-- defunR is the defunctionalizer for R
--
defunR :: MExp -> M [Rule]
defunR (Step phi)      = counter >>= return . mktrans lhs rhs
       where (lhs,rhs) = mkrule (defunK phi)
defunR (Return e)      = counter >>= return . mktrans lhs rhs
       where (lhs,rhs) = mkrule (defunK (Return e))
defunR (Fix k vs e)    = gM >>= \ i ->
                         (rdEnvM >>= \ rho ->                  
                           inEnvM (tweek k vs rho) (defunR e)) >>= \ rs ->
                              return (mkstart k i : rs)
defunR (RecCall k es)  = rdEnvM >>= \ rho ->                  
                         let
                            fps       = rho k
                            deltas    = map (uncurry set) (zip fps es)
                            delta     = foldr (.) id deltas -- order doesn't matter here
                            (lhs,rhs) = mkrule delta
                         in
                            counter >>= return . mkrectrans lhs rhs k

defunR b@(Bind e es)   = defunR phi  >>= \ [r] ->
                         defunR next >>= \ rs ->
                            return (fudge v r : rs)
      where ((phi,v), next) = projBind b
            fudge :: Var -> Rule -> Rule
            fudge v (Rule(lhs,(i,Out,s))) = Rule(lhs,(i,Out,upd v s))

defunR (BindNull phis) = error "finish"
defunR e               = error $ "defunR doesn't handle: " ++ show e

-----------------------------------------------------
-----------------------------------------------------
-----------------------------------------------------
-----------------------------------------------------
-----------------------------------------------------

--
-- defunK is the defunctionalizer for K.
--
defunK :: MExp -> State -> State
defunK Get                    = \ (State x1 x2 x3 x4 x5 x6) -> 
                                      (State x1 x2 x3 x4 x5 x5)
defunK (Store e)              = \ s@(State x1 x2 x3 x4 x5 x6) -> 
                                      (State x1 x2 x3 x4 (eval e s) NilVal)
defunK (Return e)             = \ s@(State x1 x2 x3 x4 x5 x6) -> 
                                      (State x1 x2 x3 x4 x5 (eval e s))
defunK ActionA                = \ s@(State x1 x2 x3 x4 x5 x6) ->
                                let
                                   x5' = eval (Plus (Name "reg") (Lit 1)) s
                                in 
                                   State x1 x2 x3 x4 x5' NilVal
defunK ActionB                = \ s@(State x1 x2 x3 x4 x5 x6) ->
                                let
                                   x5' = eval (Sub (Name "reg") (Lit 1)) s
                                in 
                                   State x1 x2 x3 x4 x5' NilVal
defunK (BindNull cs)          = foldr (.) id (reverse $ map defunK cs)
defunK b@(Bind e es)          =  defunK next . bind (phi,v)
         where ((phi,v), next) = projBind b
               bind (e,v)      = (upd v . defunK e)
defunK e                      = error $ "What the heck is " ++ show e ++ "?"

projBind :: MExp -> ((MExp,Var),MExp)
projBind (Bind e ((v,e'):[])) = ((e,v),e')
projBind (Bind e ((v,e'):es)) = ((e,v),Bind e' es)

upd :: Var -> State -> State
upd x (State a b a' b' r v) = case x of
                                   "a"    -> (State v b a' b' r v) 
                                   "b"    -> (State a v a' b' r v) 
                                   "newa" -> (State a b v b' r v)
                                   "newb" -> (State a b a' v r v)
                                   "v"    -> (State a b a' b' r r)
                                   _      -> error $ "What the hell? " ++ x

set :: Var -> Exp -> State -> State
set x y s@(State a b a' b' r v) = 
        let 
            y' = eval y s
        in
            case x of
                 "a"    -> (State y' b a' b' r v) 
                 "b"    -> (State a y' a' b' r v) 
                 "newa" -> (State a b y'  b' r v)
                 "newb" -> (State a b a' y'  r v)
                 "v"    -> (State a b a' b' r v)
                 _      -> error $ "Huh? " ++ x


pi :: Var -> State -> Exp
pi "a" (State x1 x2 x3 x4 x5 x6)    = x1
pi "b" (State x1 x2 x3 x4 x5 x6)    = x2
pi "newa" (State x1 x2 x3 x4 x5 x6) = x3
pi "newb" (State x1 x2 x3 x4 x5 x6) = x4
pi "reg" (State x1 x2 x3 x4 x5 x6)  = x5
pi "val" (State x1 x2 x3 x4 x5 x6)  = x6

eval :: Exp -> State -> Exp
eval e c = case e of
                (Name v)     -> pi v c
                (Init v)     -> e
                (Lit i)      -> e
                (Plus e1 e2) -> Plus e1' e2'
                    where e1' = eval e1 c
                          e2' = eval e2 c
                (Sub e1 e2)  -> Sub e1' e2'
                    where e1' = eval e1 c
                          e2' = eval e2 c
                NilVal       -> NilVal

init0 = State (Init "a0") 
              (Init "b0") 
              (Init "newa0") 
              (Init "newb0") 
              (Init "reg0") 
              (Init "val0")

mkrule delta = (init0,delta init0)

-----------------------------------------------------
-----------------------------------------------------
-------         Formatting Considerations     -------
-----------------------------------------------------
-----------------------------------------------------

pretty :: [Rule] -> IO () 
pretty [] = putStr "\n"
pretty (Rule(lhs,rhs):rs) = ppstate lhs >> 
                            putStr " -> " >> 
                            ppstate rhs >> 
                            putStr "\n" >> 
                            pretty rs
   where ppstate (i,io,s)                = putStr $
                                           "(" ++ show i ++ "," 
                                              -- ++ show io ++ "," 
                                               ++ showState s 
                                               ++ ")"
         showState (State a b a' b' r v) =    show a  ++ ","
                                           ++ show b  ++ ","
                                           ++ show a' ++ ","
                                           ++ show b' ++ ","
                                           ++ show r  ++ ","
                                           ++ show v 

rule2FSM (Rule((i,io,s),(i',io',s'))) = 
            do 
              putStrLn ""
              putStrLn $ "state_" 
                         ++ show i 
                         ++ " -> state_" 
                         ++ show i'
                         ++ " where "
              putStrLn "{"
              stateFSM s s'
              putStrLn "}"

stateFSM (State a b newa newb r v) (State a' b' newa' newb' r' v') =
      printtrans $ concat (map mpair (zip [a,b,newa,newb,r,v] [a',b',newa',newb',r',v']))
   where
       mpair (x,y) = if x == y then [] else [(y,x)]
       printtrans []           = return () 
       printtrans ((e,e'):eps) = putStrLn ("\t" ++ show e' ++ "' <= " ++ show e ++ ";")  >>
                                 printtrans eps
