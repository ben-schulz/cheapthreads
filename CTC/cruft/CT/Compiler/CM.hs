module CT.Compiler.CM where

import qualified Data.Monoid
import qualified Data.Tuple
import qualified Data.Either
--
-- Regular declarations
--

--
-- NOTE: Due to a limitation in MonadLab you will have to take the output
-- CM.hs and change this line:
--
--     module CM where
--
-- to:
--
--     module CT.Compiler.CM where
--
import CT.Syntax
import CT.Compiler.ThreeAddressCode
import Data.Maybe
import Data.List
------------------
------------------
-- Symbol table --
------------------
------------------
type FunTab     = [FunSpec]
data FunSpec    = FunSpec {
   funSpecName     :: CtsIdent,
   funSpecArgNames :: [CtsIdent],
   funSpecArgTys   :: [CtsType],
   funSpecRetTy    :: CtsType,
   funSpecBody     :: CtsExpr
}
--------------------------
--------------------------
-- Monad specifications --
--------------------------
--------------------------
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
type MonadStateEnv = [((CtsIdent,CtsIdent),Register)]
        
------------------------------
------------------------------
-- Data type specifications --
------------------------------
------------------------------
type DTTab      = [DTSpec]
data DTSpec     = DTSpec {
   dtSpecName     :: CtsIdent,
   dtSpecConSpecs :: [ConSpec]
} deriving Show
data ConSpec    = ConSpec {
   conSpecName :: CtsIdent,
   conSpecTys  :: [CtsType]
} deriving Show
----------------------------------
----------------------------------
-- "Kappa" context for fixpoint --
----------------------------------
----------------------------------
data Kappa = Kappa {
   kappaName   :: CtsIdent,
   kappaSpSave :: Register,
   kappaLabel  :: Label,
   kappaRegs   :: [Register]
} deriving Show
--                                        --
-- Miscellaneous support functions follow --
--                                        --
-- Seems weird that there's no prelude function for this
lookupBy :: (Eq b) => (a -> b) -> b -> [a] -> Maybe a
lookupBy f k xs = lookup k [(f x,x) | x <- xs]
-- Maps a data constructor to its tag
getCtorTag :: CtsIdent -> CM Int
getCtorTag ident = do
                      dttab  <- rdDTTabCM
                      
                      let dt =  fromMaybe (error $ "undefined constructor " ++ ident)
                                          (find (elem ident . map conSpecName . dtSpecConSpecs) dttab)
                      
                      let t  =  fromJust $ elemIndex ident (map conSpecName (dtSpecConSpecs dt))
                                         
                      return t
-- Maps a type constructor to its data type specification
getDTSpec :: CtsIdent -> CM DTSpec
getDTSpec name = do
                    dttab  <- rdDTTabCM
                    let sp =  fromMaybe (error $ "undefined data type " ++ name)
                                        (lookupBy dtSpecName name dttab)
                    return sp
       
-- Maps a data constructor to its constructor specification
getConSpec :: CtsIdent -> CM ConSpec
getConSpec name = do
                     dttab           <- rdDTTabCM
                     
                     let allconspecs =  concatMap dtSpecConSpecs dttab
                     let cs          =  fromMaybe (error $ "undefined constructor " ++ name)
                                                  (lookupBy conSpecName name allconspecs)
                                               
                     return cs
-- Maps a data constructor to its data type specification
getDTSpecByCtor :: CtsIdent -> CM DTSpec
getDTSpecByCtor name = do
                          dttab      <- rdDTTabCM
                          
                          let dtHasCtor :: DTSpec -> Bool
                              dtHasCtor dt = any (==name) (map conSpecName (dtSpecConSpecs dt))
                          let dtspec    =  fromMaybe (error $ "undefined constructor " ++ name)
                                                     (find dtHasCtor dttab)
                          return dtspec
-- Maps a function name to its function specification
getFunSpec :: CtsIdent -> CM FunSpec
getFunSpec name = do
                     funtab  <- rdFunTabCM
                     let tsp =  fromMaybe (error $ "No type signature for function " ++ name)
                                          (lookupBy funSpecName name funtab)
                                           
                     return tsp
--------------------
--------------------
-- Local bindings --
--------------------
--------------------
type BindEnv = [Binding]
data Binding    = Binding {
   bindingName :: CtsIdent,
   bindingTy   :: CtsType,
   bindingReg  :: Register
} deriving Show
---------------------------------------
---------------------------------------
-- Generating fresh labels/registers --
---------------------------------------
---------------------------------------
freshNumCM :: CM Int
freshNumCM = do
                lc <- getLabelCountCM
                putLabelCountCM (lc+1)
                return lc


--
-- Monad declarations
--

newtype CM a = CM {deCM :: ((->) CtsSrcPos
                                 ((->) FunTab
                                       ((->) MonadEnv
                                             ((->) MonadStateEnv
                                                   ((->) BindEnv
                                                         ((->) DTTab
                                                               (Int ->
                                                                (->) (Maybe Kappa)
                                                                     ((a, Int)))))))))}
instance Prelude.Monad CM
    where return = \x_0 -> CM (\r_1 -> \r_2 -> \r_3 -> \r_4 -> \r_5 -> \r_6 -> \s_7 -> \r_8 -> (x_0,
                                                                                                s_7))
          (>>=) = \x_9 -> \f_10 -> CM $ (\r_11 -> \r_12 -> \r_13 -> \r_14 -> \r_15 -> \r_16 -> \s0_17 -> \r_18 -> (\(v_19,
                                                                                                                              s1_20) -> deCM (f_10 v_19) r_11 r_12 r_13 r_14 r_15 r_16 s1_20) (deCM x_9 r_11 r_12 r_13 r_14 r_15 r_16 s0_17 r_18) r_18)
rdSrcPosCM = CM $ (\r_21 -> \r_22 -> \r_23 -> \r_24 -> \r_25 -> \r_26 -> \s_27 -> \r_28 -> (r_21,
                                                                                                     s_27))
inSrcPosCM = \r_29 -> \m_30 -> CM $ (\_ -> deCM m_30 r_29)
rdFunTabCM = CM $ (\r_31 -> \r_32 -> \r_33 -> \r_34 -> \r_35 -> \r_36 -> \s_37 -> \r_38 -> (r_32,
                                                                                                     s_37))
inFunTabCM = \r_39 -> \m_40 -> CM $ (\r'_41 -> \_ -> deCM m_40 r'_41 r_39)
rdMonadEnvCM = CM $ (\r_42 -> \r_43 -> \r_44 -> \r_45 -> \r_46 -> \r_47 -> \s_48 -> \r_49 -> (r_44,
                                                                                                       s_48))
inMonadEnvCM = \r_50 -> \m_51 -> CM $ (\r'_52 -> \r'_53 -> \_ -> deCM m_51 r'_52 r'_53 r_50)
rdMonadStateEnvCM = CM $ (\r_54 -> \r_55 -> \r_56 -> \r_57 -> \r_58 -> \r_59 -> \s_60 -> \r_61 -> (r_57,
                                                                                                            s_60))
inMonadStateEnvCM = \r_62 -> \m_63 -> CM $ (\r'_64 -> \r'_65 -> \r'_66 -> \_ -> deCM m_63 r'_64 r'_65 r'_66 r_62)
rdBindEnvCM = CM $ (\r_67 -> \r_68 -> \r_69 -> \r_70 -> \r_71 -> \r_72 -> \s_73 -> \r_74 -> (r_71,
                                                                                                      s_73))
inBindEnvCM = \r_75 -> \m_76 -> CM $ (\r'_77 -> \r'_78 -> \r'_79 -> \r'_80 -> \_ -> deCM m_76 r'_77 r'_78 r'_79 r'_80 r_75)
rdDTTabCM = CM $ (\r_81 -> \r_82 -> \r_83 -> \r_84 -> \r_85 -> \r_86 -> \s_87 -> \r_88 -> (r_86,
                                                                                                    s_87))
inDTTabCM = \r_89 -> \m_90 -> CM $ (\r'_91 -> \r'_92 -> \r'_93 -> \r'_94 -> \r'_95 -> \_ -> deCM m_90 r'_91 r'_92 r'_93 r'_94 r'_95 r_89)
getLabelCountCM = CM (\r_96 -> \r_97 -> \r_98 -> \r_99 -> \r_100 -> \r_101 -> \s_102 -> \r_103 -> (s_102,
                                                                                                   s_102))
putLabelCountCM = \x_104 -> CM (\r_105 -> \r_106 -> \r_107 -> \r_108 -> \r_109 -> \r_110 -> \_ -> \r_111 -> ((),
                                                                                                             x_104))
updateLabelCountCM = \f_112 -> getLabelCountCM >>= (\s_113 -> putLabelCountCM (f_112 s_113) >> getLabelCountCM)
rdKappaCM = CM $ (\r_114 -> \r_115 -> \r_116 -> \r_117 -> \r_118 -> \r_119 -> \s_120 -> \r_121 -> (r_121,
                                                                                                            s_120))
inKappaCM = \r_122 -> \m_123 -> CM $ (\r'_124 -> \r'_125 -> \r'_126 -> \r'_127 -> \r'_128 -> \r'_129 -> \s_130 -> \_ -> deCM m_123 r'_124 r'_125 r'_126 r'_127 r'_128 r'_129 s_130 r_122)
runCM = \x_131 -> \q_132 q_133 q_134 q_135 q_136 q_137 q_138 q_139 -> (Data.Tuple.fst . id) (deCM x_131 q_132 q_133 q_134 q_135 q_136 q_137 q_138 q_139)
