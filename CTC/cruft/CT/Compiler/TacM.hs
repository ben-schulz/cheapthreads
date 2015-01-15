module CT.Compiler.TacM where

import qualified Data.Monoid
import qualified Data.Tuple
import qualified Data.Either
--
-- Regular declarations
--

import CT.Compiler.ThreeAddressCode
type Word     = Int
type Loc      = Int
type Code     = PC -> TacCommand
type LabelMap = Label -> PC
type PC       = Int
type RegFile  = Register -> Word
type Memory   = Loc -> Word


--
-- Monad declarations
--

newtype TacM a = TacM {deTacM :: ((->) Code
                                       ((->) LabelMap
                                             (PC ->
                                              RegFile ->
                                              Memory ->
                                              IO ((((a, PC), RegFile), Memory)))))}
instance Prelude.Monad TacM
    where return = \x_0 -> TacM (\r_1 -> \r_2 -> \s_3 -> \s_4 -> \s_5 -> return (((x_0,
                                                                                            s_3),
                                                                                           s_4),
                                                                                          s_5))
          (>>=) = \x_6 -> \f_7 -> TacM $ (\r_8 -> \r_9 -> \s0_10 -> \s0_11 -> \s0_12 -> (>>=) (deTacM x_6 r_8 r_9 s0_10 s0_11 s0_12) (\(v_13,
                                                                                                                                                          s1_14) -> (\(v_15,
                                                                                                                                                                       s1_16) -> (\(v_17,
                                                                                                                                                                                    s1_18) -> deTacM (f_7 v_17) r_8 r_9 s1_18) v_15 s1_16) v_13 s1_14))
rdCodeTacM = TacM $ (\r_19 -> \r_20 -> \s_21 -> \s_22 -> \s_23 -> return (((r_19,
                                                                                              s_21),
                                                                                             s_22),
                                                                                            s_23))
inCodeTacM = \r_24 -> \m_25 -> TacM $ (\_ -> deTacM m_25 r_24)
rdLabelMapTacM = TacM $ (\r_26 -> \r_27 -> \s_28 -> \s_29 -> \s_30 -> return (((r_27,
                                                                                                  s_28),
                                                                                                 s_29),
                                                                                                s_30))
inLabelMapTacM = \r_31 -> \m_32 -> TacM $ (\r'_33 -> \_ -> deTacM m_32 r'_33 r_31)
getPCTacM = TacM (\r_34 -> \r_35 -> \s_36 -> \s_37 -> \s_38 -> return (((s_36,
                                                                                  s_36),
                                                                                 s_37),
                                                                                s_38))
putPCTacM = \x_39 -> TacM (\r_40 -> \r_41 -> \_ -> \s_42 -> \s_43 -> return ((((),
                                                                                        x_39),
                                                                                       s_42),
                                                                                      s_43))
updatePCTacM = \f_44 -> getPCTacM >>= (\s_45 -> putPCTacM (f_44 s_45) >> getPCTacM)
getRegFileTacM = TacM (\r_46 -> \r_47 -> \s_48 -> \s0_49 -> \s0_50 -> (>>=) (return ((s0_49,
                                                                                                        s0_49),
                                                                                                       s0_50)) (\(v_51,
                                                                                                                  s1_52) -> (\(v_53,
                                                                                                                               s1_54) -> \s_55 -> return (((v_53,
                                                                                                                                                                     s_48),
                                                                                                                                                                    s1_54),
                                                                                                                                                                   s_55)) v_51 s1_52))
putRegFileTacM = \x_56 -> TacM (\r_57 -> \r_58 -> \s_59 -> \s0_60 -> \s0_61 -> (>>=) (return (((),
                                                                                                                 x_56),
                                                                                                                s0_61)) (\(v_62,
                                                                                                                           s1_63) -> (\(v_64,
                                                                                                                                        s1_65) -> \s_66 -> return (((v_64,
                                                                                                                                                                              s_59),
                                                                                                                                                                             s1_65),
                                                                                                                                                                            s_66)) v_62 s1_63))
updateRegFileTacM = \f_67 -> getRegFileTacM >>= (\s_68 -> putRegFileTacM (f_67 s_68) >> getRegFileTacM)
getMemoryTacM = TacM (\r_69 -> \r_70 -> \s_71 -> \s0_72 -> \s0_73 -> (>>=) ((>>=) (return (s0_73,
                                                                                                                      s0_73)) (\(v_74,
                                                                                                                                 s1_75) -> return ((v_74,
                                                                                                                                                             s0_72),
                                                                                                                                                            s1_75))) (\(v_76,
                                                                                                                                                                        s1_77) -> (\(v_78,
                                                                                                                                                                                     s1_79) -> \s_80 -> return (((v_78,
                                                                                                                                                                                                                           s_71),
                                                                                                                                                                                                                          s1_79),
                                                                                                                                                                                                                         s_80)) v_76 s1_77))
putMemoryTacM = \x_81 -> TacM (\r_82 -> \r_83 -> \s_84 -> \s0_85 -> \s0_86 -> (>>=) ((>>=) (return ((),
                                                                                                                               x_81)) (\(v_87,
                                                                                                                                         s1_88) -> return ((v_87,
                                                                                                                                                                     s0_85),
                                                                                                                                                                    s1_88))) (\(v_89,
                                                                                                                                                                                s1_90) -> (\(v_91,
                                                                                                                                                                                             s1_92) -> \s_93 -> return (((v_91,
                                                                                                                                                                                                                                   s_84),
                                                                                                                                                                                                                                  s1_92),
                                                                                                                                                                                                                                 s_93)) v_89 s1_90))
updateMemoryTacM = \f_94 -> getMemoryTacM >>= (\s_95 -> putMemoryTacM (f_94 s_95) >> getMemoryTacM)
liftIOTacM = TacM . ((\m_96 -> \r_97 -> m_96) . ((\m_98 -> \r_99 -> m_98) . ((\m_100 -> \s_101 -> \s0_102 -> \s0_103 -> (>>=) (m_100 s0_102 s0_103) (\(v_104,
                                                                                                                                                                                           s1_105) -> (\(v_106,
                                                                                                                                                                                                         s1_107) -> \s_108 -> return (((v_106,
                                                                                                                                                                                                                                                 s_101),
                                                                                                                                                                                                                                                s1_107),
                                                                                                                                                                                                                                               s_108)) v_104 s1_105)) . ((\m_109 -> \s_110 -> \s0_111 -> (>>=) (m_109 s0_111) (\(v_112,
                                                                                                                                                                                                                                                                                                                                                   s1_113) -> return ((v_112,
                                                                                                                                                                                                                                                                                                                                                                                s_110),
                                                                                                                                                                                                                                                                                                                                                                               s1_113))) . ((\m_114 -> \s_115 -> (>>=) m_114 (\v_116 -> return (v_116,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                           s_115))) . id)))))
runTacM = \x_117 -> \q_118 q_119 q_120 q_121 q_122 -> deTacM x_117 q_118 q_119 q_120 q_121 q_122 >>= (\v_123 -> return ((Data.Tuple.fst . (Data.Tuple.fst . (Data.Tuple.fst . id))) v_123))
