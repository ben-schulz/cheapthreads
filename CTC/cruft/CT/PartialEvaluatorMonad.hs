module CT.PartialEvaluatorMonad where

import qualified Data.Monoid
import qualified Data.Tuple
import qualified Data.Either
--
-- Regular declarations
--

import CT.Syntax
type Environment = [(CtsIdent,CtsExpr)]
type Closure = (CtsExpr,Environment)
type Functions = [(CtsIdent,([CtsIdent],CtsExpr))]


--
-- Monad declarations
--

newtype EM a = EM {deEM :: ((->) Environment ((->) Functions a))}
instance Prelude.Monad EM
    where return = \x_0 -> EM (\r_1 -> \r_2 -> x_0)
          (>>=) = \x_3 -> \f_4 -> EM $ (\r_5 -> \r_6 -> deEM (f_4 (deEM x_3 r_5 r_6)) r_5 r_6)
rdEnvironmentEM = EM $ (\r_7 -> \r_8 -> r_7)
inEnvironmentEM = \r_9 -> \m_10 -> EM $ (\_ -> deEM m_10 r_9)
rdFunctionsEM = EM $ (\r_11 -> \r_12 -> r_12)
inFunctionsEM = \r_13 -> \m_14 -> EM $ (\r'_15 -> \_ -> deEM m_14 r'_15 r_13)
runEM = \x_16 -> \q_17 q_18 -> id (deEM x_16 q_17 q_18)
