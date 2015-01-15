--
-- this is ~/cheapthreads/ctc/ct/defunctionalization/defunm.hs
--
-- a copy of ~/cheapthreads/ctc/ct/defunctionalization/DefunMonad.hs
--
-- with types modified for consistency with new defunctionalizer
--
-- put here 12.02.09
--
-- Schulz

module CT.Defunctionalizer.DefunM where

import qualified Data.Monoid
import qualified Data.Tuple
import qualified Data.Either
--
-- Regular declarations
--

import CT.Syntax

--
-- type declarations very slightly changed for consistency
-- with new code
--
type Name = String
type Var = String
type Bindings = Var -> [Var]
type TypeBindings = [(Name, CtsType)]
type Code = [(Name, CtsExpr)]

-- old type declarations:

--type Bindings     = Var -> [Var]
--type Var          = String
--type TypeBindings = [(Name, CtType)]
--type Code         = [(Name, CtExp)]


--
-- Monad declarations
--

newtype M a = M {deM :: ((->) Bindings
                              (Int -> (->) TypeBindings ((->) Code ((a, Int)))))}
instance Prelude.Monad M
    where return = \x_0 -> M (\r_1 -> \s_2 -> \r_3 -> \r_4 -> (x_0,
                                                               s_2))
          (>>=) = \x_5 -> \f_6 -> M $ (\r_7 -> \s0_8 -> \r_9 -> \r_10 -> (\(v_11,
                                                                                     s1_12) -> deM (f_6 v_11) r_7 s1_12) (deM x_5 r_7 s0_8 r_9 r_10) r_9 r_10)
rdEnvM = M $ (\r_13 -> \s_14 -> \r_15 -> \r_16 -> (r_13,
                                                            s_14))
inEnvM = \r_17 -> \m_18 -> M $ (\_ -> deM m_18 r_17)
getStoM = M (\r_19 -> \s_20 -> \r_21 -> \r_22 -> (s_20, s_20))
putStoM = \x_23 -> M (\r_24 -> \_ -> \r_25 -> \r_26 -> ((),
                                                        x_23))
updateStoM = \f_27 -> getStoM >>= (\s_28 -> putStoM (f_27 s_28) >> getStoM)
rdTypM = M $ (\r_29 -> \s_30 -> \r_31 -> \r_32 -> (r_31,
                                                            s_30))
inTypM = \r_33 -> \m_34 -> M $ (\r'_35 -> \s_36 -> \_ -> deM m_34 r'_35 s_36 r_33)
rdCodeM = M $ (\r_37 -> \s_38 -> \r_39 -> \r_40 -> (r_40,
                                                             s_38))
inCodeM = \r_41 -> \m_42 -> M $ (\r'_43 -> \s_44 -> \r'_45 -> \_ -> deM m_42 r'_43 s_44 r'_45 r_41)
runM = \x_46 -> \q_47 q_48 q_49 q_50 -> (Data.Tuple.fst . id) (deM x_46 q_47 q_48 q_49 q_50)
