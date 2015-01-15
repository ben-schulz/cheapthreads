--
-- ETIC interpreter/denotational semantics
--

module ETIC.Interp where

import ETIC.Syntax
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State

---------------
-- The monad --
---------------
type M = StateT Sta (ReaderT Env Identity)

-- ETIC values
data ETICVal = ETICInt Int
             | ETICBool Bool
             | ETICChar Char
             | ETICString String
             | ETICTCB TCB
             deriving Show

type TCB = () -- FIXME: Stub!

-- State consists of a store and a location counter
data Sta = Sta
           {
             store  :: Store,
             locCtr :: Loc
           }

-- A store is a mapping from locations to values
type Store = Loc -> ETICVal
type Loc   = Int

-- Utility functions for stores.

-- Generate a fresh location.
freshLoc :: M Loc
freshLoc = modify (\ sta -> sta { locCtr = locCtr sta + 1 }) >> liftM locCtr get

-- Store value v at location l.
storeVal :: Loc -> ETICVal -> M ()
storeVal l v = modify (\ sta -> sta { store = tweek (store sta) l v })

-- Environment is maps of names to function definitions
-- (these are a global thing) and variable bindings (be
-- they global or local).
data Env = Env
           {
             varBindings :: Identifier -> Loc,
             funDefns    :: Identifier -> FunDefn
           }

type Identifier = String

-- Definition of a function
-- NOTE: I'm carrying "env" around here because I want
--       to be able to "roll back" the environment to
--       what it was when the function was defined; i.e.,
--       if a function f or variable v is defined AFTER
--       function g in the source text, we do not want
--       f or v (or g!) to be available in the body of g.
--       This has the effect of disallowing recursion.
data FunDefn = FunDefn
               {
                 env    :: Env,
                 mRetTy :: Maybe Type, -- FIXME: needed?
                 name   :: Identifier, -- FIXME: needed?
                 params :: [(Type,Identifier)],
                 locals :: [VarDecl],
                 body   :: [Stmt]
               }

-- Utility functions for environments.

askVarBindings :: M (Identifier -> Loc)
askVarBindings = ask >>= return . varBindings

localVarBindings :: ((Identifier -> Loc) -> (Identifier -> Loc)) -> M a -> M a
localVarBindings d = local (\ env -> env { varBindings = d (varBindings env) })

askFunDefns :: M (Identifier -> FunDefn)
askFunDefns = ask >>= return . funDefns

-- Utility functions on stores/environments.
tweek :: (Eq a) => (a -> b) -> a -> b -> (a -> b)
tweek m k v = \ k' -> if k' == k then v else m k'

extend :: (Eq a) => (a -> b) -> [(a,b)] -> a -> b
extend = foldr tweekPair
         where tweekPair (k,v) m = tweek m k v

---------------------
-- The interpreter --
---------------------

-- To get out of the monad
interp prog = runIdentity $ runReaderT (runStateT (interpProg prog) initSta) initEnv
              where
                initSta = Sta
                          {
                            store  = \ l -> error $ "Uninitialized location " ++ show l,
                            locCtr = 0
                          }
                initEnv = Env
                          {
                            varBindings = \ v -> error $ "Unbound variable " ++ v,
                            funDefns    = \ f -> error $ "Undeclared function " ++ f
                          }

-- Main entry point: just set up the initial environment/store, and
-- call main.
interpProg :: Prog -> M (Maybe ETICVal)
interpProg (Prog decls) = interpTopDecls decls >>= \ env ->
                          local (const env) (interpStmt (Return $ FunCall "main" []))

-- Before we start execution, we need to set up the initial environment
-- and initialize global variables. We make a pass over the TopDecls to
-- do this.
interpTopDecls :: [TopDecl] -> M Env
interpTopDecls (d:ds) = interpTopDecl d >>= \ env ->
                        local (const env) (interpTopDecls ds)
interpTopDecls []     = ask

interpTopDecl :: TopDecl -> M Env
-- FIXME: ignoring modifiers and type (maybe OK if it passed typechecker?)
interpTopDecl (TopVarDecl vd) = interpVarDecl vd
-- IODecl unneeded
-- ImageDecl unneeded
interpTopDecl (FunDecl mRetTy name params locals body) = ask >>= \ env ->
                                                         let
                                                            funDefn = FunDefn
                                                                      {
                                                                        env    = env,
                                                                        mRetTy = mRetTy,
                                                                        name   = name,
                                                                        params = params,
                                                                        locals = locals,
                                                                        body   = body
                                                                      }
                                                         in
                                                            return (env { funDefns = tweek (funDefns env) name funDefn })
-- HandlerDecl unneeded for now
-- UnionDec
-- StructDec
-- EnumDec

-- This is used for TopDecls as well as function-locals, so
-- we'll break it out separately.
interpVarDecl :: VarDecl -> M Env
interpVarDecl (VarDecl _ _ x mE) = ask      >>= \ env ->
                                   freshLoc >>= \ l ->
                                   (case mE of
                                     (Just e) -> interpExpr e >>= \ v ->
                                                 storeVal l v
                                     Nothing  -> return ())  >>
                                   return (env { varBindings = tweek (varBindings env) x l })

-- Interpreter for expressions.
interpExpr :: Expr -> M ETICVal
interpExpr (Var x)       = askVarBindings >>= \ bindings ->
                           get            >>= \ sta ->
                             return $ (store sta) (bindings x)
interpExpr (VarIX x e)   = error "VarIX"
interpExpr (LitInt i)    = return (ETICInt $ fromIntegral i)
interpExpr (LitBool b)   = return (ETICBool b)
interpExpr (LitChar c)   = return (ETICChar c)
interpExpr (LitString s) = return (ETICString s)
interpExpr (Add e1 e2)   = interpExpr e1 >>= \ v1 ->
                           interpExpr e2 >>= \ v2 ->
                           case (v1,v2) of
                             (ETICInt i1,ETICInt i2) -> return (ETICInt (i1+i2))
                             _                       -> error "Add"
interpExpr (Sub e1 e2)   = interpExpr e1 >>= \ v1 ->
                           interpExpr e2 >>= \ v2 ->
                           case (v1,v2) of
                             (ETICInt i1,ETICInt i2) -> return (ETICInt (i1-i2))
                             _                       -> error "Sub"
interpExpr (Mul e1 e2)   = interpExpr e1 >>= \ v1 ->
                           interpExpr e2 >>= \ v2 ->
                           case (v1,v2) of
                             (ETICInt i1,ETICInt i2) -> return (ETICInt (i1*i2))
                             _                       -> error "Mul"
interpExpr (Div e1 e2)   = interpExpr e1 >>= \ v1 ->
                           interpExpr e2 >>= \ v2 ->
                           case (v1,v2) of
                             (ETICInt _,ETICInt 0)   -> error "Div0"
                             (ETICInt i1,ETICInt i2) -> return (ETICInt (i1 `div` i2))
                             _                       -> error "Div"
interpExpr (Modulus e1 e2) = interpExpr e1 >>= \ v1 ->
                             interpExpr e2 >>= \ v2 ->
                             case (v1,v2) of
                               (ETICInt _,ETICInt 0)   -> error "Mod0"
                               (ETICInt i1,ETICInt i2) -> return (ETICInt (i1 `mod` i2))
                               _                       -> error "Mod"
interpExpr (Neg e)       = interpExpr e >>= \ v ->
                           case v of
                             (ETICBool b) -> return (ETICBool (not b))
                             _            -> error "Neg"
-- AndLogic,OrLogic,Not,IsLT,IsGT,IsLTE,IsGTE,IsEq,NotEq,AndBit,OrBit,XorBit,ShiftL,ShiftR,NotBit
interpExpr (FunCall name args) = askFunDefns >>= \ defns ->
                                 let
                                    funDefn  = defns name
                                    fEnv     = env funDefn
                                    parNames = map snd (params funDefn)
                                 in
                                    -- FIXME: Should check # args (though again typechecker should catch any problems)
                                    -- FIXME: Need to set up locals
                                    mapM interpExpr args               >>= \ vs ->
                                    replicateM (length args) freshLoc  >>= \ ls ->
                                    sequence_ (zipWith storeVal ls vs) >>
                                    -- Roll back environment to f's environment...
                                    local (const fEnv)
                                     -- ...and extend that with bindings for the params.
                                     (localVarBindings 
                                      (\ bdgs -> extend bdgs (zip parNames ls))
                                      (interpStmts (body funDefn))) >>= \ mv ->
                                    case mv of
                                      (Just v) -> return v
                                      Nothing  -> error "No value returned from function"
-- PCBAccess unneeded *** Since PCBs are first-class vals now
-- MemAccess unneeded
-- Image stuff unneeded
-- CtorApp unneeded
-- StructMember
-- UnionMember
-- MkPair unneeded
-- MkThread

-- Interpreter for statements. Since we have "return" statements inside
-- functions this is slightly wonky; rather than Stmt -> M () for
-- interpStmt, we have M (Maybe ETICVal), where a non-return statement
-- will just return Nothing. In interpStmts we map interpStmt over a
-- list of Stmts, but stop when (and if) one of them returns a value.
--
-- Annoying FIXME: Actually there are also DeclStmts, which can alter
-- the *environment*, so the return type may have to get even hairier.
interpStmts :: [Stmt] -> M (Maybe ETICVal)
interpStmts (s:ss) = interpStmt s >>= \ mv ->
                     case mv of
                       (Just v) -> return (Just v)
                       Nothing  -> interpStmts ss
interpStmts []     = return Nothing

interpStmt :: Stmt -> M (Maybe ETICVal)
interpStmt (ExprStmt e)          = interpExpr e >> return Nothing
-- DeclStmt
interpStmt (Assign (LHSVar x) e) = interpExpr e            >>= \ v ->
                                   askVarBindings          >>= \ bindings ->
                                   storeVal (bindings x) v >>
                                     return Nothing
-- Assign LHSVarIX
-- Assign LHSPCB unneeded *** Since PCBs are first-class vals now
-- Assign LHSMEM unneeded
-- IOStmt unneeded
-- Case
-- MatchUnion unneeded
interpStmt (IfThenElse e st msf) = interpExpr e >>= \ v ->
                                   case v of
                                     (ETICBool True)  -> interpStmts st
                                     (ETICBool False) -> case msf of
                                                           (Just sf) -> interpStmts sf
                                                           Nothing   -> return Nothing
                                     _                -> error "IfThenElse"
-- While
-- Loop
-- Break
-- Jump
interpStmt (Return e)            = interpExpr e >>= return . Just
interpStmt Skip                  = return Nothing