
module RPSLam.ULamParser where

import Text.ParserCombinators.Parsec
import Data.Char

import RPSLam.EssenceSyn

ulparse :: String -> Term
ulparse s = let p = runParser
                    (
                      term >>= \t ->
                      spaces >>
                      (spaces <|> eof) >>
                      return t
                    ) () "" s

            in
              case p of
                (Right s') -> s'
                (Left e) -> error $ show e ++ "\nin:\n" ++ s

term :: Parser Term
term = spaces >>

       (
         (many1 digit >>= \ds -> return (Con $ atoi ds))
         <|> lam
         <|> try ifzero
         <|> try var
         <|> ((char '(') >> term >>= \t ->  (char ')') >> return t)
       ) >>= \t ->

       (
         (try (spaces >> term >>= \t' -> return $ App t t'))
         <|> return t
       )

lam :: Parser Term
lam = try (char '\\') >>
      spaces >>
      sym >>= \x ->
      spaces >>
      (string "->") >>
      spaces >>
      term >>= \t ->
      return $ Lam x t

app :: Parser Term
app = term >>= \t ->
      spaces >>
      term >>= \t' ->
      return $ App t t'

ifzero :: Parser Term
ifzero = spaces >>
         string "IFZERO" >>
         spaces >>
         term >>= \t ->
         case t of
           (App t (App t' t'')) -> return (IFZERO t t' t'')

var :: Parser Term
var = sym >>= \x -> return $ Var x

sym :: Parser String
sym = many1 alphaNum

--
-- String to Int, assuming a well-formed string:
--
atoi :: String -> Int
atoi ('-':ds) = negate $ atoi ds
atoi ds = foldl (\n -> \d -> (digitToInt d) + 10 * n) 0 ds

