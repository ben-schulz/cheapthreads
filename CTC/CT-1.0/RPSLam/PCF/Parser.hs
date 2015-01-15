
module PCF.Parser where

import Text.ParserCombinators.Parsec
import Data.Char

import PCF.Syntax

data LTerm = LAM String Term
           | MU String Term
           | TM Term

pcfparse :: String -> Term
pcfparse s = let p = runParser
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
       -- if-then-else case:
       (

         string "if" >>
         spaces >>
         (char '(' >> term >>= \t -> spaces >> char ')' >> return t) >>= \t ->
         spaces >>
         string "then" >>
         spaces >>
         (char '(' >> term >>= \t -> spaces >> char ')' >> return t) >>= \t' ->
         spaces >>
         string "else" >>
         spaces >>
         (char '(' >> term >>= \t -> spaces >> char ')' >> return t) >>= \t'' ->
         return (EF t t' t'')
         
       )
       <|>

       ((
         many1
         (
          (
           mu
           <|> lam
           <|> try inc
           <|> try dec
           <|> try ztest
           <|> (many1 digit >>= \ds -> return (TM $ Con $ atoi ds))
           <|> try bool
           <|> try var
           <|> ((char '(') >> term >>= \t ->  (char ')') >> return (TM t))

          ) >>= \t -> spaces >> return t

         ) >>= \ts ->

         return (lassoc ts)
       )

       ))


lam :: Parser LTerm
lam = try (char '\\') >>
      spaces >>
      sym >>= \x ->
      spaces >>
      (string "->") >>
      spaces >>
      term >>= \t ->
      return $ LAM x t

mu :: Parser LTerm
mu = try (char 'u') >>
     spaces >>
     sym >>= \x ->
     spaces >>
     (string "->") >>
     spaces >>
     term >>= \t ->
     return $ MU x t

app :: Parser Term
app = spaces >>
      term >>= \t ->
      spaces >>
      term >>= \t' ->
      return (App t t')

ef :: Parser LTerm
ef = try (string "if") >>
     spaces >>
     term >>= \t ->
     spaces >>
     string " then" >>
     spaces >>
     term >>= \t' ->
     spaces >>
     string "else" >>
     spaces >>
     term >>= \t'' ->
     spaces >>
     return (TM (EF t t' t''))

inc :: Parser LTerm
inc = try (string "1+") >>
      spaces >>
      term >>= \t ->
      return $ TM (Inc t)

dec :: Parser LTerm
dec = try (string "1-") >>
      spaces >>
      term >>= \t ->
      return $ TM (Dec t)


var :: Parser LTerm
var = sym >>= \x ->
      return (TM (Var x))

sym :: Parser String
sym = many1 alphaNum


bool :: Parser LTerm
bool = ((string "true") <|> (string "false")) >>= \s ->
       case s of
         "false" -> return (TM (Bit False))
         "true"  -> return (TM (Bit True))

ztest :: Parser LTerm
ztest = string "zero?" >>
        spaces >>
        term >>= \t ->
        spaces >>
        return (TM (ZTest t))

--
-- left-associate application
--
lassoc :: [LTerm] -> Term
lassoc (t:ts) = foldl
                  (\t -> \l -> App t (toterm l))
                    (toterm t) ts

toterm :: LTerm -> Term
toterm (LAM x t) = Lam x t
toterm (MU x t)  = Mu x t
toterm (TM t)    = t


--
-- String to Int, assuming a well-formed string:
--
atoi :: String -> Int
atoi ('-':ds) = negate $ atoi ds
atoi ds = foldl (\n -> \d -> (digitToInt d) + 10 * n) 0 ds

