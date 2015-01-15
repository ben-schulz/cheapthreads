module Codegen.ETICGen where

import CT.TypeChecker
import Data.List
import ETIC.Syntax
import Codegen.CgMonad
import CT.Syntax
import CT.ANAST
import Data.Maybe

type FunName = String
type ParamName = String
type Params = [ParamName]
type LamLift = (FunName,Params)

--This only works when there's one function named main >_<

--evalprog :: ANProg -> Cg ()

evalprog [(("main", _), (xs, a))] = do
                           lams <- evalTLam a
                           let decls = map (\x -> TopVarDecl (VarDecl [] TyInt x Nothing)) lams
                           innerAST <- evalOapp a
                           stmts <- inEMapCg [("!CURFUN","main")] (eval innerAST)
                           fundecs <- getFDeclsCg
                           liftIOCg $ putStrLn (show fundecs)
                           let fxndecs = map snd $ filter (\(x,_) -> if x == "main" then True else False) fundecs
                           let mainfxn = FunDecl Nothing "main" [] fxndecs stmts 
                           let prog = (Prog (decls ++ [mainfxn]))
                           liftIOCg $ putStrLn (show prog)
                           return ()
                           
                           
                           
--This is mostly a dry run to see how I can write a quick thing to transform SimpleKernel.ct.hs into some kind
--of ETIC 
evalTLam :: ANAST -> Cg ([String])
evalTLam (CTLamAN a b _ ) = do 
                                res <- evalTLam b
                                return $ [a] ++ res
evalTLam _ = return []

evalOApp :: ANAST -> Cg (ANAST)
evalOapp (CTLamAN a b _) = evalOApp b
evalOApp ast = return ast


eval :: ANAST -> Cg ([Stmt])  
eval (CTAppAN a (CTVarAN var _) _) = do --Stick apps onto a queue, each successive lam pulls it off and maps it
                                        idents <- rdAppsCg
                                        let newEnv = idents ++ [var]
                                        inAppsCg newEnv (eval a)
       
eval (CTFixAN (CTLamAN ident ast _) _) = do
                                             idents <- rdEMapCg
                                             let cFun = fromJust $ lookup "!CURFUN" idents
                                             let newEnv = idents ++ [(ident,"!FIXLOOP")] -- note that K is a fix loop
                                             curDecls <- getFDeclsCg
                                             let newDecls = curDecls ++ [(cFun,(VarDecl [] TyBool ident (Just (ETIC.Syntax.LitInt 1) )))]
                                             putFDeclsCg newDecls
                                             loopbody <- inEMapCg newEnv (eval ast)
                                             return [(While (Var ident) ([(Assign (LHSVar ident) (ETIC.Syntax.LitInt 0))] ++ loopbody))]

--VarDecl [Modifier] Type String (Maybe Expr) deriving Show
eval (CTLamAN ident ast _) = do
                                apps <- rdAppsCg
                                envMap <- rdEMapCg
                                let mapVar = head apps
                                let newApps = if (length apps) > 0 then (tail apps) else []
                                let newEnvM = envMap ++ [(ident,mapVar)]
                                inAppsCg newApps (inEMapCg newEnvM (eval ast)) -- pull an app off the queue and map it to the lam
eval (CTNullBindAN a b _) = do
                             bodyA <- eval a
                             bodyB <- eval b
                             return (bodyA ++ bodyB)

eval (CTStepAN (CTVarAN var _) _)       = do  -- run stuff and put it on the queue here, pid = a
                                             currEnv <- rdEMapCg
                                             let rvar = resVar var currEnv
                                             return [ExprStmt (FunCall "step" [(Var rvar)])]
           
eval (CTVarAN ident _) = do  --- this is going to be an apply of a jumpback to a fix in our case right now
                            return [(Assign (LHSVar ident) (ETIC.Syntax.LitInt 1))] -- if we're at the end, it should just be an empty list.
eval a = error (show a)

lamLift :: ANAST -> LamLift -> (LamLift,ANAST)
lamLift (CTLamAN ident ast _) (fname,ps) = lamLift ast (fname ++ ident, ps ++ [ident])
lamLift a b = (b,a) -- If we don't see another Lam, we're done merging them into a list and jump to the code body in the AST

--Lifting in Applies this time
appLift :: ANAST -> Params -> (Params,ANAST)
appLift (CTAppAN ast (CTVarAN a _) _) (ps) = appLift ast (ps ++ [a])
appLift a b = (b,a) -- If we don't see another Lam, we're done merging them into a list and jump to the code body in the AST

--
resVar :: String -> [(String,String)] -> String
resVar a xs = case (lookup a xs) of
                Nothing -> a
                (Just x) -> x
              
