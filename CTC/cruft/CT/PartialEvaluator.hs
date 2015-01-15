module CT.PartialEvaluator where

import CT.Syntax
import Data.List
import Data.Maybe
import Control.Monad
import CT.PartialEvaluatorMonad

isVal :: CtsExpr -> EM Bool
isVal (CtsConstrApp _ es _) = (liftM and) (mapM isVal es)
isVal (CtsLitExpr _ _)      = return True
isVal (CtsTuple es _)       = (liftM and) (mapM isVal es)
isVal (CtsList es _)        = (liftM and) (mapM isVal es)
isVal (CtsUnit _)           = return True
isVal (CtsReturn e _)       = isVal e
isVal _                     = return False

evalCase :: [CtsAlt] -> CtsExpr -> EM CtsExpr
evalCase alts (CtsTuple es ty)          = case matchingAlt of
                                             (Just (CtsAlt (CtsPTuple xs) e)) -> do
                                                                                    rho <- rdEnvironmentEM
                                                                                    let rho' = zip xs es ++ rho
                                                                                    inEnvironmentEM rho' (eval e)
                                             Nothing                          -> return (CtsTuple es ty)
                                           where
                                             matchingAlt                       = find isMatch alts
                                             isMatch (CtsAlt (CtsPTuple xs) _) = length es == length xs
                                             isMatch _                         = False
evalCase alts (CtsConstrApp ctor es ty) = case matchingAlt of
                                             (Just (CtsAlt (CtsPConstr _ xs) e)) -> do
                                                                                       rho <- rdEnvironmentEM
                                                                                       let rho' = zip xs es ++ rho
                                                                                       inEnvironmentEM rho' (eval e)
                                             Nothing                             -> return (CtsConstrApp ctor es ty)
                                           where
                                             matchingAlt                              = find isMatch alts
                                             isMatch (CtsAlt (CtsPConstr ctor' xs) _) = ctor == ctor'
                                             isMatch _                                = False

inlineApp :: CtsExpr -> EM CtsExpr
inlineApp (CtsApp f es ty) = do
                                functions <- rdFunctionsEM
                                let defn = lookup f functions
                                case defn of
                                   (Just (xs,e')) -> do
                                                        let letBindings = zip xs es
                                                        e'' <- inEnvironmentEM [] (eval e')
                                                        return (CtsLet letBindings e'' ty)
                                   Nothing        -> return (CtsApp f es ty)

eval :: CtsExpr -> EM CtsExpr
-- FIXME: Currently this is all or nothing; if all the arguments are static,
--        then we will PE; otherwise we inline with a "let". Should instead
--        do a polyvariant division, but this is okay for now.
eval e@(CtsApp f es ty)        = do
                                    es'       <- mapM eval es
                                    es'Vals   <- (liftM and) (mapM isVal es')
                                    if es'Vals
                                      then do
                                        functions <- rdFunctionsEM
                                        let defn  =  lookup f functions
                                        case defn of
                                           (Just (xs,e')) -> do
                                                                let rho' = zip xs es'
                                                                inEnvironmentEM rho' (eval e')
                                           Nothing        -> return (CtsApp f es' ty)
                                      else inlineApp (CtsApp f es' ty)
-- FIXME
eval (CtsFixApp xs b args ty)  = do
                                    b'    <- eval b
                                    args' <- mapM eval args
                                    return (CtsFixApp xs b' args' ty)
eval (CtsInfixApp e1 op e2 ty) = do
                                    e1' <- eval e1
                                    e2' <- eval e2
                                    case (e1',op,e2') of
                                       (CtsLitExpr (CtsLitInt x) _,"+",CtsLitExpr (CtsLitInt y) _) -> return $ CtsLitExpr (CtsLitInt (x+y)) TyInt
                                       (CtsLitExpr (CtsLitInt x) _,"-",CtsLitExpr (CtsLitInt y) _) -> return $ CtsLitExpr (CtsLitInt (x-y)) TyInt
                                       (CtsLitExpr (CtsLitInt x) _,">",CtsLitExpr (CtsLitInt y) _) -> return $ CtsLitExpr (CtsLitBool (x>y)) TyBool
                                       (CtsLitExpr (CtsLitInt x) _,"<",CtsLitExpr (CtsLitInt y) _) -> return $ CtsLitExpr (CtsLitBool (x<y)) TyBool
                                       (CtsLitExpr (CtsLitInt x) _,"==",CtsLitExpr (CtsLitInt y) _) -> return $ CtsLitExpr (CtsLitBool (x==y)) TyBool
-- FIXME                                       (eCar,":",CtsList esCdr tyCdr)                              ->
                                       _                                                           -> return $ CtsInfixApp e1' op e2' ty
eval (CtsConstrApp ctor es ty) = do
                                    es' <- mapM eval es
                                    return (CtsConstrApp ctor es' ty)
eval e@(CtsLitExpr _ _)        = return e
eval e@(CtsVar x ty)           = do
                                    rho <- rdEnvironmentEM
                                    case lookup x rho of
                                       (Just e') -> return e'
                                       -- Might be a nullary function, so we check for that too.
                                       Nothing  ->
                                          do
                                             functions <- rdFunctionsEM
                                             case lookup x functions of
                                                (Just ([],e')) -> inEnvironmentEM [] (eval e')
                                                Nothing        -> return e
eval (CtsNeg e ty)             = do
                                    e' <- eval e
                                    case e' of
                                       (CtsLitExpr (CtsLitInt x) _) -> return (CtsLitExpr (CtsLitInt (-x)) ty)
                                       _                            -> return (CtsNeg e' ty)
eval (CtsIfThenElse e t f ty)  = do
                                    e' <- eval e
                                    t' <- eval t
                                    f' <- eval f
                                    case e' of
                                       (CtsLitExpr (CtsLitBool True) _)  -> return t'
                                       (CtsLitExpr (CtsLitBool False) _) -> return f'
                                       _                                 -> return (CtsIfThenElse e' t' f' ty)
eval (CtsCase e alts ty)       = do

                                    e'      <- eval e
                                    e'IsVal <- isVal e'
                                    if e'IsVal
                                       then evalCase alts e'
                                       else do
                                         let evalAlt :: CtsAlt -> EM CtsAlt
                                             evalAlt (CtsAlt (CtsPTuple xs) e)       = do
                                                                                          rho <- rdEnvironmentEM
                                                                                          let rho' = filter (\(x,_) -> not (x `elem` xs)) rho
                                                                                          e' <- inEnvironmentEM rho' (eval e)
                                                                                          return (CtsAlt (CtsPTuple xs) e')
                                             evalAlt (CtsAlt (CtsPConstr ctor xs) e) = do
                                                                                          rho <- rdEnvironmentEM
                                                                                          let rho' = filter (\(x,_) -> not (x `elem` xs)) rho
                                                                                          e' <- inEnvironmentEM rho' (eval e)
                                                                                          return (CtsAlt (CtsPConstr ctor xs) e')
                                         alts' <- mapM evalAlt alts
                                         return $ CtsCase e' alts' ty
eval (CtsTuple es ty)          = do
                                    es' <- mapM eval es
                                    return (CtsTuple es' ty)
eval (CtsList es ty)           = do
                                    es' <- mapM eval es
                                    return (CtsList es' ty)
eval e@(CtsUnit ty)            = return e
eval e@(CtsEmptyList ty)       = return e
eval (CtsBind e1 x e2 ty)      = do
                                    e1'            <- eval e1
                                    case e1' of
                                       (CtsReturn e1'b _) -> do
                                                                rho <- rdEnvironmentEM
                                                                let rho' = (x,e1'b):rho
                                                                inEnvironmentEM rho' $ eval e2
                                       _                  -> do
                                                                rho <- rdEnvironmentEM
                                                                let rho' = filter (\(x',_) -> x /= x') rho
                                                                e2' <- inEnvironmentEM rho' (eval e2)
                                                                return (CtsBind e1' x e2' ty)
eval (CtsBindNull e1 e2 ty)    = do
                                    e1' <- eval e1
                                    e2' <- eval e2
                                    e1'Val <- isVal e1'
                                    if e1'Val
                                      then return e2'
                                      else return (CtsBindNull e1' e2' ty)
eval (CtsReturn e ty)          = do
                                    e' <- eval e
                                    return (CtsReturn e' ty)

pe :: CtsProg -> CtsProg
pe (CtsProg decls) = let
                        peIfMain (CtsFunDecl pos f xs e) = let
                                                              rho       = []
                                                              functions = concatMap extractFunctions decls
                                                              e'        = runEM (eval e) rho functions
                                                           in
                                                              CtsFunDecl pos f xs e'
                        peIfMain d                            = d
                        decls' = map peIfMain decls
                     in
                        CtsProg decls'

extractFunctions :: CtsDecl -> Functions
extractFunctions (CtsFunDecl _ f xs e) = [(f,(xs,e))]
extractFunctions (CtsRecDecl ds)       = concatMap extractFunctions ds
extractFunctions _                     = []
