module CommonTypes where

import DefunMonad

type A  = Int
type B  = Int
--type G  = Int

data Label = ILab Int | VLab Var
instance Show Label where
     show (ILab i) = show i
     show (VLab k) = k
data Value = Nil | Z Int
data InOut = In | Out deriving (Show,Eq)
data State = State Exp -- a
                   Exp -- b
                   Exp -- newa
                   Exp -- newb
                   Exp -- r
                   Exp -- v

-- MExp is the source language
-- What about return?

data MExp = Fix Var [Var] MExp       -- fix (\ k -> \ vs -> e)
          | Step MExp                -- in (Step phi), phi :: K a
          | BindNull [MExp]          -- >>
          | Bind MExp [(Var,MExp)]   -- >>=
          | Upd StateTransform       -- update f = \ s -> (f s,f s). Isn't "u".
          | Get                      -- i.e., \ sigma -> (sigma,sigma)
          | Store Exp -- Var         -- sets reg <- Var
          | ActionA                  -- reg++
          | ActionB                  -- reg--
          | RecCall Var [Exp]        -- Recursive calls
          | Return Exp
     deriving Show

-- chan :: A -> B -> R ()
-- chan = fix (\ k -> \ a -> \ b -> step (store a >> actionA >> g) >>= \ newa -> 
--                                  step (store b >> actionB >> g) >>= \ newb -> 
--                                     k newa newb)

-- This is the reified channel code
rchan = Fix "k" ["a","b"] body
   where body = Bind (Step $ BindNull [Store (Name "a"),ActionA,Get]) [("newa",
                     (Step $ BindNull [Store (Name "b"),ActionB,Get])), ("newb",
                     RecCall "k" [Name "newa",Name "newb"])]

{-
actionA = Bind (Step $ Get) [("newa",Step $ Store e)]
     where t =  (Just "r" :|-> e)
           e = (Plus (Name "newa") (Lit 1))
-}

--actionA = Bind Get [("newa",Store e)]
--     where e = (Plus (Name "newa") (Lit 1))

foo0 = BindNull [Store (Name "a"),ActionA,Get]

foo1 = Bind (Step Get) [("newa",(Step (Store (Plus (Name "newa") (Lit 9)))))]

foo2 = Bind Get [("newa",Store (Plus (Name "newa") (Lit 9)))]

foo3 = Store (Plus (Name "newa") (Lit 9))

data Rule = Rule ((Label,InOut,State),(Label,InOut,State))

-- The Maybe means that we allow wildcard patterns "_"
data StateTransform = (Maybe Var) :|-> Exp deriving Show
data Exp = Lit Int | Plus Exp Exp | Sub Exp Exp 
         | Name Var | NilVal | Init Var deriving Eq
--
-- (Init x) is not a regular expression (i.e., it's not truly part of the
-- language. It signifies that x is a initial value, not to be further evaluated.
--

instance Show Exp where
   show (Lit i)      = show i
   show (Plus e1 e2) = show e1 ++ "+" ++ show e2
   show (Sub e1 e2)  = show e1 ++ "-" ++ show e2
   show (Name v)     = v
   show (Init v)     = v
   show NilVal       = "()"


instance Show State where
    show (State a b a' b' r v) = "(" ++ show a  ++ ","
                                     ++ show b  ++ ","
                                     ++ show a' ++ ","
                                     ++ show b' ++ ","
                                     ++ show r  ++ ","
                                     ++ show v  ++ ")"

instance Show Value where
    show Nil   = "()"
    show (Z i) = show i


-- Here's the new view of states
data NewState = NewState Int 
                         InOut 
                         Exp 
                         [Exp] -- represent args to fix-vars
                         [Exp] -- represent lambda vars
                         [Exp] -- states defined in the monad
