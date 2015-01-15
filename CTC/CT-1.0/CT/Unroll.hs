module CT.Unroll where

import CT.Syntax
import CT.INAST
import Control.Monad.Identity
import Control.Monad.Reader
import System.IO.Unsafe
import Data.Maybe
import Debug.Trace

doUnroll :: INProg -> INProg
doUnroll p = runUM (unrollProg p) (mkEnv p)

type UM = ReaderT Env Identity

type Env = String -> Binding
data Binding = Unbound | Bound INAST deriving Show

runUM :: UM a -> Env -> a
runUM m initEnv = runIdentity (runReaderT m initEnv)

mkEnv :: INProg -> Env
mkEnv (INProg ((maindec,fundecs),_)) =
      foldr (\(INFunDec ((f,_),(args,b))) -> bind f (mkLam b args)) emptyEnv fundecs
      where
        mkLam = foldr (\ arg -> \ e -> (CTLamIN arg e CTUnitTy)) -- FIXME: Will need to do the correct thing with annotation here

emptyEnv :: Env
emptyEnv = const Unbound

unbind :: String -> Env -> Env
unbind x env = \ v -> if v==x then Unbound else env v

bind :: String -> INAST -> Env -> Env
bind x e env = \ v -> if v==x then Bound e else env v

deleteAll :: (Eq a) => a -> [a] -> [a]
deleteAll x = filter (/=x)

fv :: INAST -> [String]
fv (CTAppIN e1 e2 _)           = fv e1 ++ fv e2
-- CTRecAppIN...
-- CTFixAppIN...
fv (CTLamIN x e _)             = deleteAll x (fv e)
fv (CTBindIN e1 e2 _)          = fv e1 ++ fv e2
fv (CTNullBindIN e1 e2 _)      = fv e1 ++ fv e2
fv (CTReturnIN e _)            = fv e
fv (CTGetIN _ _)               = []
fv (CTPutIN _ e _)             = fv e
--CTReadIN...
--CTWriteIN...
fv (CTStepIN e _)              = fv e
fv (CTFixIN e _)               = fv e
fv (CTSignalIN e _)            = fv e
fv (CTPrim1aryIN _ e _)        = fv e
fv (CTPrim2aryIN _ e1 e2 _)    = fv e1 ++ fv e2
fv (CTPrim3aryIN _ e1 e2 e3 _) = fv e1 ++ fv e2 ++ fv e3
fv (CTBranchIN e1 e2 e3 _)     = fv e1 ++ fv e2 ++ fv e3
fv (CTCaseIN e alts _)         = fv e ++ concatMap fvAlt alts
fv (CTPairIN e1 e2 _)          = fv e1 ++ fv e2
fv (CTListIN es _)             = concatMap fv es
fv (CTVarIN x _)               = [x]
fv (CTConIN _ es _)            = concatMap fv es
fv (CTLitIN _ _)               = []
fv (CTUnitIN _)                = []

fvAlt :: (CTPat,INAST) -> [String]
fvAlt (p,e) = foldr deleteAll (fv e) (patVars p)

patVars :: CTPat -> [String]
patVars (PLit _ _)       = []
patVars (PVar x _)       = [x]
patVars (PTuple p1 p2 _) = patVars p1 ++ patVars p2
patVars (PList ps _)     = concatMap patVars ps
patVars (PCon _ ps _)    = concatMap patVars ps
patVars (PPause p _)     = patVars p
patVars (PDone p _)      = patVars p
patVars (PCons p1 p2 _)  = patVars p1 ++ patVars p2
patVars (PNest p _)      = patVars p
patVars (Wildcard _)     = []

maybeUnroll :: INAST -> UM INAST
maybeUnroll (CTAppIN (CTVarIN "unroll" _) e _) = unroll e >>= \ e' ->
                                                 return e'
maybeUnroll (CTAppIN e1 e2 an) = maybeUnroll e1 >>= \ e1' ->
                                 maybeUnroll e2 >>= \ e2' ->
                                 return (CTAppIN e1' e2' an)
maybeUnroll (CTRecAppIN e1 e2 an) = maybeUnroll e1 >>= \ e1' ->
                                    maybeUnroll e2 >>= \ e2' ->
                                    return (CTRecAppIN e1' e2' an)
maybeUnroll (CTFixAppIN e es an) = maybeUnroll e       >>= \ e' ->
                                   mapM maybeUnroll es >>= \ es' ->
                                   return (CTFixAppIN e' es' an)
maybeUnroll (CTLamIN x e an) = maybeUnroll e >>= \ e' ->
                               return (CTLamIN x e' an)
maybeUnroll (CTBindIN e1 e2 an) = maybeUnroll e1 >>= \ e1' ->
                                  maybeUnroll e2 >>= \ e2' ->
                                  return (CTBindIN e1' e2' an)
maybeUnroll (CTNullBindIN e1 e2 an) = maybeUnroll e1 >>= \ e1' ->
                                      maybeUnroll e2 >>= \ e2' ->
                                      return (CTNullBindIN e1' e2' an)
maybeUnroll (CTReturnIN e an)       = maybeUnroll e >>= \ e' ->
                                      return (CTReturnIN e' an)
maybeUnroll e@(CTGetIN _ _) = return e
maybeUnroll (CTPutIN x e an) = maybeUnroll e >>= \ e' ->
                               return (CTPutIN x e' an)

maybeUnroll (CTReadIN x e t) = maybeUnroll e >>= \e' ->
                               return (CTReadIN x e' t)

maybeUnroll (CTWriteIN x i e t) = maybeUnroll e >>= \e' ->
                                  maybeUnroll i >>= \i' ->
                                  return (CTWriteIN x i' e' t)


maybeUnroll (CTStepIN e an) = maybeUnroll e >>= \ e' ->
                              return (CTStepIN e' an)
maybeUnroll (CTFixIN e an) = maybeUnroll e >>= \ e' ->
                             return (CTFixIN e' an)
maybeUnroll (CTSignalIN e an) = maybeUnroll e >>= \ e' ->
                                return (CTSignalIN e' an)
maybeUnroll (CTPrim1aryIN op e an) = maybeUnroll e >>= \ e' ->
                                     return (CTPrim1aryIN op e' an)
maybeUnroll (CTPrim2aryIN op e1 e2 an) = maybeUnroll e1 >>= \ e1' ->
                                         maybeUnroll e2 >>= \ e2' ->
                                         return (CTPrim2aryIN op e1' e2' an)
maybeUnroll (CTPrim3aryIN op e1 e2 e3 an) = maybeUnroll e1 >>= \ e1' ->
                                            maybeUnroll e2 >>= \ e2' ->
                                            maybeUnroll e3 >>= \ e3' ->
                                            return (CTPrim3aryIN op e1' e2' e3' an)
maybeUnroll (CTBranchIN e1 e2 e3 an) = maybeUnroll e1 >>= \ e1' ->
                                       maybeUnroll e2 >>= \ e2' ->
                                       maybeUnroll e3 >>= \ e3' ->
                                       return (CTBranchIN e1' e2' e3' an)
maybeUnroll (CTCaseIN e alts an) = maybeUnroll e            >>= \ e' ->
                                   mapM maybeUnrollAlt alts >>= \ alts' ->
                                   return (CTCaseIN e' alts' an)
maybeUnroll (CTPairIN e1 e2 an) = maybeUnroll e1 >>= \ e1' ->
                                  maybeUnroll e2 >>= \ e2' ->
                                  return (CTPairIN e1' e2' an)
maybeUnroll (CTListIN es an) = mapM maybeUnroll es >>= \ es' ->
                               return (CTListIN es' an)
maybeUnroll e@(CTVarIN _ _) = return e
maybeUnroll (CTConIN x es an) = mapM maybeUnroll es >>= \ es' ->
                                return (CTConIN x es' an)
maybeUnroll e@(CTLitIN _ _) = return e
maybeUnroll e@(CTUnitIN _) = return e

--maybeUnroll x = error $ show x


maybeUnrollAlt :: (CTPat, INAST) -> UM (CTPat, INAST)
maybeUnrollAlt (pat,e) = maybeUnroll e >>= \ e' ->
                         return (pat,e')

isUnBound :: Env -> String -> Bool
isUnBound env x = case env x of
                    Unbound -> True
                    _       -> False


unrollByLeftIdentity :: INAST -> INAST -> UM (Maybe INAST)
unrollByLeftIdentity (CTReturnIN e _)                     (CTLamIN x b _) = {-trace ("**** DIDIT :::: " ++ show e ++ show b) $-} local (bind x e) (liftM Just $ unroll b)
unrollByLeftIdentity (CTBindIN e1 (CTLamIN x e2 an2) an1) e               = unrollByLeftIdentity e2 e >>= \ mE2u ->
                                                                            case mE2u of
                                                                              (Just e2u) -> return (Just $ CTBindIN e1 (CTLamIN x e2u an2) an1)
                                                                              Nothing    -> return Nothing
unrollByLeftIdentity (CTNullBindIN e1 e2 an)              e               = unrollByLeftIdentity e2 e >>= \ mE2u ->
                                                                            case mE2u of
                                                                              (Just e2u) -> return (Just $ CTNullBindIN e1 e2u an)
                                                                              Nothing    -> return Nothing
unrollByLeftIdentity leaf                                 _               = return Nothing

unroll :: INAST -> UM INAST
unroll (CTAppIN e1 e2 an)            = unroll e1 >>= \ e1' ->
                                       unroll e2 >>= \ e2' ->
                                       ask       >>= \ env ->
                                       case e1' of
                                         (CTLamIN x b _) -> local (bind x e2') (unroll b)
                                         _               -> return (CTAppIN e1' e2' an)
--unroll (CTRecAppIN e1 e2 an)         =
--unroll (CTFixAppIN e es an)          =
unroll (CTLamIN x e an)              = local (unbind x) (unroll e) >>= \ e' ->
                                       return (CTLamIN x e' an)
unroll (CTBindIN e1 e2 an)           = unroll e1 >>= \ e1' ->
                                       unroll e2 >>= \ e2' ->
                                       unrollByLeftIdentity e1 e2 >>= \ mE1u ->
                                           case mE1u of
                                             (Just e1u) -> unroll e1u
                                             Nothing    -> return (CTBindIN e1' e2' an)
unroll (CTNullBindIN e1 e2 an)       = unroll e1 >>= \ e1' ->
                                       unroll e2 >>= \ e2' ->
                                       return (CTNullBindIN e1' e2' an)
unroll (CTReturnIN e an)             = unroll e >>= \ e' ->
                                       return (CTReturnIN e' an)
unroll e@(CTGetIN _ _)               = return e
unroll (CTPutIN x e an)              = unroll e >>= \ e' ->
                                       return (CTPutIN x e' an)
unroll (CTReadIN lbl e an)           = unroll e >>= \ e' ->
                                       return (CTReadIN lbl e' an)
unroll (CTWriteIN lbl e1 e2 an)      = unroll e1 >>= \ e1' ->
                                       unroll e2 >>= \ e2' ->
                                       return (CTWriteIN lbl e1' e2' an)
unroll (CTStepIN e an)               = unroll e >>= \ e' ->
                                       return (CTStepIN e' an)
unroll (CTFixIN e an)                = unroll e >>= \ e' ->
                                       return (CTFixIN e' an)
unroll (CTSignalIN e an)             = unroll e >>= \ e' ->
                                       return (CTSignalIN e' an)
unroll (CTPrim1aryIN op e an)        = unroll e >>= \ e' ->
                                       case (op,e') of
                                         (Un CTNeg,CTLitIN (LitInt i) t)  -> return (CTLitIN (LitInt (-i)) t)
                                         (Un CTNot,CTLitIN (LitBool b) t) -> return (CTLitIN (LitBool (not b)) t)
                                         (Un Fst,CTPairIN e _ _)          -> return e
                                         (Un Snd,CTPairIN _ e _)          -> return e
                                         _                                -> return (CTPrim1aryIN op e' an)
unroll (CTPrim2aryIN op e1 e2 an)    = unroll e1 >>= \ e1' ->
                                       unroll e2 >>= \ e2' ->
                                       case (op,e1',e2') of
                                         (Bin CTCons,_,CTListIN es t) -> return (CTListIN (e1':es) t)
                                         (Bin CTPlus,CTLitIN (LitInt i1) CTIntTy ,CTLitIN (LitInt i2) CTIntTy)
                                                                      -> return (CTLitIN (LitInt (i1+i2)) CTIntTy)
                                         (Bin CTMinus,CTLitIN (LitInt i1) CTIntTy ,CTLitIN (LitInt i2) CTIntTy)
                                                                      -> return (CTLitIN (LitInt (i1-i2)) CTIntTy)
                                         (Bin CTMult,CTLitIN (LitInt i1) CTIntTy ,CTLitIN (LitInt i2) CTIntTy)
                                                                      -> return (CTLitIN (LitInt (i1*i2)) CTIntTy)
                                         (Bin CTIDiv,CTLitIN (LitInt i1) CTIntTy ,CTLitIN (LitInt i2) CTIntTy)
                                                                      -> return (CTLitIN (LitInt (i1 `div` i2)) CTIntTy)
                                         (Bin CTExpn,CTLitIN (LitInt i1) CTIntTy ,CTLitIN (LitInt i2) CTIntTy)
                                                                      -> return (CTLitIN (LitInt (i1^i2)) CTIntTy)

                                         (Bin CTAnd,CTLitIN (LitBool b1) CTBoolTy,CTLitIN (LitBool b2) CTBoolTy)
                                                                      -> return (CTLitIN (LitBool (b1&&b2)) CTBoolTy)
                                         (Bin CTOr,CTLitIN (LitBool b1) CTBoolTy,CTLitIN (LitBool b2) CTBoolTy)
                                                                      -> return (CTLitIN (LitBool (b1||b2)) CTBoolTy)

                                         (Bin CTEqTest,CTLitIN l1 _,CTLitIN l2 _)
                                                                      -> return (CTLitIN (LitBool (l1==l2)) CTBoolTy)
                                         (Bin CTIneqTest,CTLitIN l1 _,CTLitIN l2 _)
                                                                      -> return (CTLitIN (LitBool (l1/=l2)) CTBoolTy)
                                         (Bin CTLTTest,CTLitIN (LitInt i1) _,CTLitIN (LitInt i2) _)
                                                                      -> return (CTLitIN (LitBool (i1<i2)) CTBoolTy)
                                         (Bin CTGTTest,CTLitIN (LitInt i1) _,CTLitIN (LitInt i2) _)
                                                                      -> return (CTLitIN (LitBool (i1>i2)) CTBoolTy)
                                         (Bin CTLTETest,CTLitIN (LitInt i1) _,CTLitIN (LitInt i2) _)
                                                                      -> return (CTLitIN (LitBool (i1<=i2)) CTBoolTy)
                                         (Bin CTGTETest,CTLitIN (LitInt i1) _,CTLitIN (LitInt i2) _)
                                                                      -> return (CTLitIN (LitBool (i1>=i2)) CTBoolTy)

                                         _                            -> return (CTPrim2aryIN op e1' e2' an)
unroll (CTPrim3aryIN op e1 e2 e3 an) = unroll e1 >>= \ e1' ->
                                       unroll e2 >>= \ e2' ->
                                       unroll e3 >>= \ e3' ->
                                       return (CTPrim3aryIN op e1' e2' e3' an)
unroll (CTBranchIN e1 e2 e3 an)      = unroll e1 >>= \ e1' ->
                                       unroll e2 >>= \ e2' ->
                                       unroll e3 >>= \ e3' ->
                                       case e1' of
                                         (CTLitIN (LitBool True) _)  -> return e2'
                                         (CTLitIN (LitBool False) _) -> return e3'
                                         _                           -> return (CTBranchIN e1' e2' e3' an)
unroll (CTCaseIN e alts an)          = unroll e                    >>= \ e' ->
                                       mapM (tryUnrollAlt e') alts >>= \ unrolled ->
                                       case msum unrolled of
                                         (Just e'') -> unroll e''
                                         Nothing    -> mapM unrollAlt alts >>= \ alts' ->
                                                       return (CTCaseIN e' alts' an)
unroll (CTPairIN e1 e2 an)           = unroll e1 >>= \ e1' ->
                                       unroll e2 >>= \ e2' ->
                                       return (CTPairIN e1' e2' an)
unroll (CTListIN es an)              = mapM unroll es >>= \ es' ->
                                       return (CTListIN es' an)
unroll (CTVarIN x an)                = ask >>= \ env ->
                                       case env x of
                                         Unbound  -> return (CTVarIN x an)
                                         Bound e' -> return e'
unroll (CTConIN x es an)             = mapM unroll es >>= \ es' ->
                                       return (CTConIN x es' an)
unroll e@(CTLitIN _ _)               = return e
unroll e@(CTUnitIN _)                = return e
unroll e                             = error $ "Can't unroll: " ++ show e

mP :: CTPat -> INAST -> Maybe [(String,INAST)]
mP (PVar v _) e   = Just [(v,e)]
mP (Wildcard _) _ = Just []
mP _ _            = Nothing

tryUnrollAlt :: INAST -> (CTPat,INAST) -> UM (Maybe INAST)
tryUnrollAlt e (PNest p _,e')                       = tryUnrollAlt e (p,e')
tryUnrollAlt e (PVar v _,e')                        = liftM Just $ local (bind v e) (unroll e')
tryUnrollAlt _ (Wildcard _,e)                       = return (Just e)
tryUnrollAlt (CTConIN ctor es _) (PCon pctor pps _,e) = let
                                                           bindings = zipWith mP pps es
                                                        in
                                                           {-seq (unsafePerformIO $ putStr "BINDINGS >>>>> " >> print bindings) $-}
                                                           if ctor == pctor && all isJust bindings
                                                             then
                                                               liftM Just $ local (\ env -> foldr (uncurry bind) env (concatMap fromJust bindings)) (unroll e)
                                                             else
                                                               return Nothing
tryUnrollAlt _ _                                    = return Nothing

unrollAlt :: (CTPat, INAST) -> UM (CTPat, INAST)
unrollAlt (pat,e) = local (\ env -> foldr unbind env (patVars pat)) (unroll e) >>= \ e' ->
                    return (pat,e')

unrollFunDec :: INFunDec -> UM INFunDec
unrollFunDec (INFunDec ((f,ty),(args,b))) =
             local (\ env -> foldr unbind env args) (maybeUnroll b) >>= \ b' ->
             return (INFunDec ((f,ty),(args,b')))

unrollProg :: INProg -> UM INProg
unrollProg (INProg ((maindec,fundecs),(datadecs,monaddecs))) =
           unrollFunDec maindec      >>= \ maindec' ->
           mapM unrollFunDec fundecs >>= \ fundecs' ->
           return (INProg ((maindec',fundecs'),(datadecs,monaddecs)))
