--
-- this is ~/cheapthreads/CTC/CT-1.0/RPSLam/PCF/Syntax.hs
--
-- syntax for the source language of the RPS demonstration compiler;
--
-- this is based on the the formulation of PCF presented in Gunter's
-- "Semantics of Programming Languages"
--
-- put here (2010.12.14)
--
-- Schulz
--

module PCF.Syntax where

import PPT

---------------------
-- Language syntax --
---------------------

type Name = String
data Term = Var Name
          | Con Int
          | Bit Bool
          | Lam Name Term
          | App Term Term

          -- the basic arithmetic operators:
          | Inc Term
          | Dec Term
          | ZTest Term

          -- the distinguished control abstractions:
          | EF Term Term Term       -- if-then-else
          | Mu Name Term            -- letrec

instance Show Term where
  show (Var x)       = x
  show (Con n)       = show n
  show (Bit b)       = show b
  show (Lam x t)     = "(\\" ++ x ++ ' ':'-':'>':' ':(show t) ++ ")"
  show (App t t')    = '(':(show t) ++ ' ':(show t') ++ ")"
  show (Inc t)       = "1+ " ++ (show t)
  show (Dec t)       = "1- " ++ (show t)
  show (ZTest t)     = "zero? " ++ (show t)
  show (EF t t' t'') = "if " ++ (show t) ++ " then " ++
                       (show t') ++ " else " ++ (show t'')
  show (Mu x t)      = "(u" ++ x ++ ' ':'-':'>':' ':(show t) ++ ")"

instance PPT Term where
  ppt = show

-- THIS IS THE END OF THE FILE --
