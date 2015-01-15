module Codegen.CgMonad where

import qualified Data.Monoid
import qualified Data.Tuple
import qualified Data.Either
--
-- Regular declarations
--

import ETIC.Syntax
type Ident = String
type DeclMap = [(Ident,VarDecl)]
type EnvSto = [(Ident, Ident)]


--
-- Monad declarations
--

newtype Cg a = Cg {deCg :: ((->) ([Ident])
                                 ((->) EnvSto
                                       ([TopDecl] ->
                                        DeclMap -> IO (((a, [TopDecl]), DeclMap)))))}
instance Prelude.Monad Cg
    where return = \x_0 -> Cg (\r_1 -> \r_2 -> \s_3 -> \s_4 -> return ((x_0,
                                                                                 s_3),
                                                                                s_4))
          (>>=) = \x_5 -> \f_6 -> Cg $ (\r_7 -> \r_8 -> \s0_9 -> \s0_10 -> (>>=) (deCg x_5 r_7 r_8 s0_9 s0_10) (\(v_11,
                                                                                                                                    s1_12) -> (\(v_13,
                                                                                                                                                 s1_14) -> deCg (f_6 v_13) r_7 r_8 s1_14) v_11 s1_12))
rdAppsCg = Cg $ (\r_15 -> \r_16 -> \s_17 -> \s_18 -> return ((r_15,
                                                                                s_17),
                                                                               s_18))
inAppsCg = \r_19 -> \m_20 -> Cg $ (\_ -> deCg m_20 r_19)
rdEMapCg = Cg $ (\r_21 -> \r_22 -> \s_23 -> \s_24 -> return ((r_22,
                                                                                s_23),
                                                                               s_24))
inEMapCg = \r_25 -> \m_26 -> Cg $ (\r'_27 -> \_ -> deCg m_26 r'_27 r_25)
getGDeclsCg = Cg (\r_28 -> \r_29 -> \s_30 -> \s_31 -> return ((s_30,
                                                                        s_30),
                                                                       s_31))
putGDeclsCg = \x_32 -> Cg (\r_33 -> \r_34 -> \_ -> \s_35 -> return (((),
                                                                              x_32),
                                                                             s_35))
updateGDeclsCg = \f_36 -> getGDeclsCg >>= (\s_37 -> putGDeclsCg (f_36 s_37) >> getGDeclsCg)
getFDeclsCg = Cg (\r_38 -> \r_39 -> \s_40 -> \s0_41 -> (>>=) (return (s0_41,
                                                                                        s0_41)) (\(v_42,
                                                                                                   s1_43) -> return ((v_42,
                                                                                                                               s_40),
                                                                                                                              s1_43)))
putFDeclsCg = \x_44 -> Cg (\r_45 -> \r_46 -> \s_47 -> \s0_48 -> (>>=) (return ((),
                                                                                                 x_44)) (\(v_49,
                                                                                                           s1_50) -> return ((v_49,
                                                                                                                                       s_47),
                                                                                                                                      s1_50)))
updateFDeclsCg = \f_51 -> getFDeclsCg >>= (\s_52 -> putFDeclsCg (f_51 s_52) >> getFDeclsCg)
liftIOCg = Cg . ((\m_53 -> \r_54 -> m_53) . ((\m_55 -> \r_56 -> m_55) . ((\m_57 -> \s_58 -> \s0_59 -> (>>=) (m_57 s0_59) (\(v_60,
                                                                                                                                                                s1_61) -> return ((v_60,
                                                                                                                                                                                            s_58),
                                                                                                                                                                                           s1_61))) . ((\m_62 -> \s_63 -> (>>=) m_62 (\v_64 -> return (v_64,
                                                                                                                                                                                                                                                                                  s_63))) . id))))
runCg = \x_65 -> \q_66 q_67 q_68 q_69 -> deCg x_65 q_66 q_67 q_68 q_69 >>= (\v_70 -> return ((Data.Tuple.fst . (Data.Tuple.fst . id)) v_70))
