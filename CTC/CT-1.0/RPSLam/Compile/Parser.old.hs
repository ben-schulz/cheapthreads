--
-- this is ~/cheapthreads/CTC/CT-1.0/RPSLam/Compile/Parser.hs
--
-- a parser for the simplified resumption language used to specify the
-- the handler portion of the RPS demonstration compiler
--
-- put here (2010.12.17)
--
-- Schulz
--


module Compile.Parser where

import Compile.Syntax

import Text.ParserCombinators.Parsec
import Data.Char


data Op = BIND
        | NBIND

rterm :: Parser TermR
rterm =

  -- parenthesized term:
  (
    spaces >>
    try (char '(') >>
    spaces >>
    rterm >>= \t ->
    spaces >>
    char ')' >>
    return t
  )


  -- if-then-else:
  <|>
  (
    string "if" >>
    string "then" >>
    string "else" >>
    return  (REta (Num 0))
  )

  <|>
  (
    ract >>= \a -> 
    spaces >>

    (
      -- bind case:
      (
        string ">>=" >>
        spaces >>
        string "\\" >>
        spaces >>
        name >>= \x ->
        spaces >>
        rterm >>= \t ->
        return (RBind x a t)
      )

      -- null bind case:
      <|>
      (
        string ">>" >>
        spaces >>
        rterm >>= \t ->
        return (RBindNull a t)
      )
      <|>
      return a
    )

  )

ract :: Parser TermR
ract =

  try 
  (
    string "callw" >>
    spaces >>
    rval >>= \v ->
    return (RetWith v)
  )

  <|>
  (
    string "return" >>
    spaces >>
    rval >>= \v -> 
    return (REta v)
  )


rval :: Parser RVal
rval =

  try (string "Wrong" >> return Wrong)

  <|>
  (many1 digit >>= \ds -> return (Num (atoi ds)))

  <|>
  (
    (string "True" <|> string "False") >>= \s ->
    case s of
      "False" -> return (Bol False)
      "True"  -> return (Bol True)
  )

  -- closure cases:
  --
  --    <*bind x, rho, t *>
  --    <*recbind x, rho, t *>
{-
  <|>
  (
    string "<*" >>
    spaces >>
    (string "bind" <|> string "recbind") >>= \b ->
    spaces >>
    name >>= \x ->
    spaces >>
    hexpr >>= \rho ->
    spaces >>
    rterm >>= \t ->
    spaces >>
    string "*>" >>
    case b of
      "bind" -> return (Cl x 
    
  )
-}

atoi :: String -> Int
atoi ('-':ds) = negate $ atoi ds
atoi ds = foldl (\n -> \d -> (digitToInt d) + 10 * n) 0 ds


name :: Parser String
name = many1 letter >>= \s -> many1 alphaNum >>= \t -> return (s ++ t)

-- THIS IS THE END OF THE FILE --
