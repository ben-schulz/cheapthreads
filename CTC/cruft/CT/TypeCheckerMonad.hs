module CT.TypeCheckerMonad where

import qualified Data.Monoid
import qualified Data.Tuple
import qualified Data.Either
--
-- Regular declarations
--

--
-- NOTE: Due to a limitation in MonadLab you will have to take the output
-- TypeChecker.hs and change this line:
--
--     module TypeCheckerMonad where
--
-- to:
--
--     module CT.TypeCheckerMonad where
--
import CT.Syntax
type BindEnv = [Binding]
data Binding = Binding {
   bindingName :: CtsIdent,
   bindingTy   :: CtsType
} deriving Show
type FunEnv = [FunSpec]
data FunSpec = FunSpec {
   funSpecName   :: CtsIdent,
   funSpecArgTys :: [CtsType],
   funSpecRetTy  :: CtsType
} deriving Show
type MonadEnv = [MonadNPM]
data MonadNPM = MonadStep {
                   monadStepBaseMonad     :: CtsIdent,
                   monadStepResultMonad   :: CtsIdent
                }
              | MonadGet {
                   monadGetMonad          :: CtsIdent,
                   monadGetStateName      :: CtsIdent,
                   monadGetStateType      :: CtsType
                }
              | MonadPut {
                   monadPutMonad          :: CtsIdent,
                   monadPutStateName      :: CtsIdent,
                   monadPutStateType      :: CtsType
                }
              | MonadReadHeap {
                   monadReadHeapMonad     :: CtsIdent,
                   monadReadHeapName      :: CtsIdent
                }
              | MonadStoreHeap {
                   monadStoreHeapMonad    :: CtsIdent,
                   monadStoreHeapName     :: CtsIdent
                }
              | MonadGetreq {
                   monadGetreqMonad       :: CtsIdent,
                   monadGetreqResultMonad :: CtsIdent,
                   monadGetreqReqType     :: CtsType
                }
              | MonadIsDone {
                   monadIsDoneMonad       :: CtsIdent,
                   monadIsDoneResultMonad :: CtsIdent
                }
              | MonadPutrsp {
                   monadPutrspMonad       :: CtsIdent,
                   monadPutrspResultMonad :: CtsIdent,
                   monadPutrspRspType     :: CtsType
                }
              | MonadSignal {
                   monadSignalMonad       :: CtsIdent,
                   monadSignalReqType     :: CtsType,
                   monadSignalRspType     :: CtsType
                }
              deriving Show
type DTEnv = [DTSpec]
data DTSpec = DTSpec {
   dtSpecName  :: CtsIdent,
   dtSpecCtors :: [CtsConDecl]
} deriving Show
data Kappa = Kappa {
   kappaName   :: CtsIdent,
   kappaArgTys :: [CtsType]
} deriving Show


--
-- Monad declarations
--

newtype TCM a = TCM {deTCM :: ((->) CtsSrcPos
                                    ((->) BindEnv
                                          ((->) FunEnv
                                                ((->) MonadEnv
                                                      ((->) DTEnv
                                                            ((->) (Maybe Kappa)
                                                                  (Either String a)))))))}
instance Prelude.Monad TCM
    where return = \x_0 -> TCM (\r_1 -> \r_2 -> \r_3 -> \r_4 -> \r_5 -> \r_6 -> Data.Either.Right x_0)
          (>>=) = \x_7 -> \f_8 -> TCM $ (\r_9 -> \r_10 -> \r_11 -> \r_12 -> \r_13 -> \r_14 -> (case deTCM x_7 r_9 r_10 r_11 r_12 r_13 r_14 of
                                                                                                            Data.Either.Left l_15 -> \r_16 -> \r_17 -> \r_18 -> \r_19 -> \r_20 -> \r_21 -> Data.Either.Left l_15
                                                                                                            Data.Either.Right r_22 -> deTCM (f_8 r_22)) r_9 r_10 r_11 r_12 r_13 r_14)
throwTypeErrorTCM = \x_23 -> TCM (\r_24 -> \r_25 -> \r_26 -> \r_27 -> \r_28 -> \r_29 -> Data.Either.Left x_23)
catchTypeErrorTCM = \x_30 -> \h_31 -> TCM $ (\r_32 -> \r_33 -> \r_34 -> \r_35 -> \r_36 -> \r_37 -> (case deTCM x_30 r_32 r_33 r_34 r_35 r_36 r_37 of
                                                                                                                 Data.Either.Left l_38 -> deTCM (h_31 l_38)
                                                                                                                 Data.Either.Right r_39 -> \r_40 -> \r_41 -> \r_42 -> \r_43 -> \r_44 -> \r_45 -> Data.Either.Right r_39) r_32 r_33 r_34 r_35 r_36 r_37)
rdSrcPosTCM = TCM $ (\r_46 -> \r_47 -> \r_48 -> \r_49 -> \r_50 -> \r_51 -> Data.Either.Right r_46)
inSrcPosTCM = \r_52 -> \m_53 -> TCM $ (\_ -> deTCM m_53 r_52)
rdBindEnvTCM = TCM $ (\r_54 -> \r_55 -> \r_56 -> \r_57 -> \r_58 -> \r_59 -> Data.Either.Right r_55)
inBindEnvTCM = \r_60 -> \m_61 -> TCM $ (\r'_62 -> \_ -> deTCM m_61 r'_62 r_60)
rdFunEnvTCM = TCM $ (\r_63 -> \r_64 -> \r_65 -> \r_66 -> \r_67 -> \r_68 -> Data.Either.Right r_65)
inFunEnvTCM = \r_69 -> \m_70 -> TCM $ (\r'_71 -> \r'_72 -> \_ -> deTCM m_70 r'_71 r'_72 r_69)
rdMonadEnvTCM = TCM $ (\r_73 -> \r_74 -> \r_75 -> \r_76 -> \r_77 -> \r_78 -> Data.Either.Right r_76)
inMonadEnvTCM = \r_79 -> \m_80 -> TCM $ (\r'_81 -> \r'_82 -> \r'_83 -> \_ -> deTCM m_80 r'_81 r'_82 r'_83 r_79)
rdDTEnvTCM = TCM $ (\r_84 -> \r_85 -> \r_86 -> \r_87 -> \r_88 -> \r_89 -> Data.Either.Right r_88)
inDTEnvTCM = \r_90 -> \m_91 -> TCM $ (\r'_92 -> \r'_93 -> \r'_94 -> \r'_95 -> \_ -> deTCM m_91 r'_92 r'_93 r'_94 r'_95 r_90)
rdKappaTCM = TCM $ (\r_96 -> \r_97 -> \r_98 -> \r_99 -> \r_100 -> \r_101 -> Data.Either.Right r_101)
inKappaTCM = \r_102 -> \m_103 -> TCM $ (\r'_104 -> \r'_105 -> \r'_106 -> \r'_107 -> \r'_108 -> \_ -> deTCM m_103 r'_104 r'_105 r'_106 r'_107 r'_108 r_102)
runTCM = \x_109 -> \q_110 q_111 q_112 q_113 q_114 q_115 -> ((\v_116 -> case v_116 of
                                                                           Data.Either.Left l_117 -> error ("TypeError" ++ " exception thrown")
                                                                           Data.Either.Right r_118 -> r_118) . id) (deTCM x_109 q_110 q_111 q_112 q_113 q_114 q_115)
