--
-- typeclass for formatted output from the various phases
-- of the CT compiler; used mostly for debugging
--
-- particular instance declarations are in their respective files
--
-- put here 2010.07.07 Schulz
--

module CT.PPT where

class PPT a where
  ppt :: a -> String


indent :: String -> String
indent = foldr (\c -> \s -> if '\n' == c then c:'\t':s else c:s) ""

instance (PPT a, PPT b) => PPT (Either a b) where
  ppt (Left r) = ppt r
  ppt (Right r) = ppt r

