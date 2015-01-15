--
-- my usual typeclass for formated output 
--
-- put here (2010.12.14)
--
-- Schulz
--

module PPT where

class PPT a where
  ppt :: a -> String


indent :: String -> String
indent = foldr (\c -> \s -> if '\n' == c then c:'\t':s else c:s) ""

