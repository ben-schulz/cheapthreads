
module Deprecated.ETIC.Print where

import Deprecated.ETIC.Syntax
import Control.Monad.Identity
import Data.List
type M = Identity

pprint :: Prog -> M String
pprint (Prog p) = genProg p;

genProg :: [TopDecl] -> M String
genProg ds = mapM genDecl ds >>= return . concat 

genDecl :: TopDecl -> M String

genDecl (TopVarDecl vd)     =  genVarDecl vd 

genDecl (IODecl ty str add) = 
            genTy ty           >>= \cTy ->
            return $ "IO " ++ cTy ++ " " ++ str ++ " at " ++ show add ++ ";\n"

genDecl (ImageDecl name loc) = 
            return $ "image " ++ name ++ " in \"" ++  loc ++ "\";\n"

genDecl (FunDecl mTy name parms lvd stmts) =
            genMTy mTy            >>= \cMTy ->
            mapM genParams parms  >>= \cParams ->
            mapM genVarDecl lvd   >>= \cLocals ->
            mapM genStmt stmts    >>= \cStmts ->
            return $ cMTy ++ " " ++ name ++
                    "(" ++ intercalate ", " cParams ++ ")\n" ++
                    "{ \n" ++
                    indent (concat cLocals) ++
                    indent (concat cStmts) ++
                    "} \n" 

genDecl (HandlerDecl spec lvd stmts)=
            genHandlerSpec spec       >>= \cHSpec ->
            mapM genVarDecl lvd       >>= \cLocals ->
            mapM genStmt stmts        >>= \cStmts ->
            return $ "handler( "  ++ cHSpec ++  ")\n" ++
                    "{ \n" ++
                    indent (concat cLocals) ++
                    indent (concat cStmts) ++
                    "}\n"

genDecl (UnionDecl n cases) = mapM genUnionCase cases >>= \ cCases ->
                              return $ "union " ++ n ++ "\n" ++
                                       "{\n" ++
                                       indent (concat cCases) ++
                                       "}\n"

genDecl (UnionDec x ts) = mapM genStructAlt ts >>= \ts' ->
                          return $ "union " ++ x ++ "\n" ++
                                   "{\n" ++
                                   indent (concat ts') ++
                                   "};\n\n"

genDecl (StructDec x ts) = mapM genStructAlt ts >>= \ts' ->
                           return $ "struct " ++ x ++ "\n" ++
                                   "{\n" ++
                                   indent (concat ts') ++
                                   "};\n\n"

genDecl (EnumDec xs) = return $
                         "enum {" ++ (intercalate ", " xs) ++ "};\n\n"

genStructAlt :: (String, Type) -> M String
genStructAlt (x, t) = genTy t >>= \t' ->
                      return $ t' ++ ' ':x ++ ";\n"

genUnionCase :: (String,[Type]) -> M String
genUnionCase (n,tys) = mapM genTy tys >>= \ cTys ->
                       return $ n ++ "(" ++ intercalate "," cTys ++ ");\n"

genVarDecl :: VarDecl -> M String
genVarDecl (VarDecl mods ty name init) = 
            mapM genMods mods  >>= \cMods ->
            genTy ty            >>= \cTy ->
            (case init of 
                Nothing -> return "" 
                (Just e) -> genExpr e >>= return . (" = " ++) 
            ) >>= \cInit ->
            return $ concatMap (++" ") cMods ++ cTy ++ " " ++  name ++ cInit ++ ";\n"            

genMTy :: Maybe Type -> M String
genMTy Nothing = return ""
genMTy (Just ty) = genTy ty

genTy :: Type -> M String

genTy (TyPair t1 t2) = genTy t1 >>= \ cT1 ->
                       genTy t2 >>= \ cT2 ->
                       return $ "pair<" ++ cT1 ++ "," ++ cT2 ++ ">"

genTy (TyQueue ty)   = genTy ty >>= \cTy ->
                       return $ "queue<" ++ cTy ++ ">"

genTy (TyStack t)    = genTy t >>= \t' ->
                       return $ "stack<" ++ t' ++ ">"

genTy (TyStruct x)   = return $ "struct " ++ x
genTy (TyUnion x)    = return $ "union " ++ x

genTy TyTCB   = return "__TCB"

genTy TyInt    = return "int"
genTy TyByte   = return "byte"
genTy TyBool   = return "bool"
genTy TyChar   = return "char"
genTy TyString = return "string"
genTy TyVoid   = return "void"

--
-- added fixed arrays
--
-- (2010.05.19) Schulz
--
genTy (TyArray n t)  = genTy t >>= \t' ->
                       return $ t' ++ '[':(show n) ++ "]"
--

genTy (TyUserDef s)  = return s

genParams :: (Type,String) -> M String
genParams (ty, name) = 
            genTy ty >>= \cTy ->
            return $ cTy ++ " " ++ name

genStmt :: Stmt -> M String
genStmt (ExprStmt e) = 
            genExpr e   >>= \cE ->
            return $ cE ++ ";\n"
genStmt (Assign lhs e)=
            genLHS lhs  >>= \cLHS ->
            genExpr e   >>= \cE ->
            return $ cLHS ++ " = " ++ cE ++ ";\n"

genStmt (SysCall e) = genExpr e >>= \s ->
                      return $ "__SYSTEM_CALL(" ++ s ++ ");\n"

genStmt (IOStmt s e) =
            genExpr e   >>= \cE ->
            return $ s ++ " <- " ++ cE ++ ";\n"
genStmt (Case e cs) = 
            genExpr e           >>= \cE ->
            mapM genCaseArm cs  >>= \cCS ->
            return $ "case " ++ cE ++ " of\n" ++
            "{ \n" ++
                indent (concat cCS) ++ 
            "}\n"
genStmt (IfThenElse e ifStmt eStmt) = 
            genExpr e           >>= \cE ->
            mapM genStmt ifStmt >>= \cIfStmt ->
            (case eStmt of
                Nothing -> return ""
                (Just eStmt) -> 
                    mapM genStmt eStmt >>= \cEStmt ->
                    return $ "else\n" ++ "{\n" ++
                                indent (concat cEStmt ) ++
                             "}\n"
            )  >>= \cElse ->
            return $ "if (" ++ cE ++ ")\n{\n" ++
                        indent (concat cIfStmt) ++
                     "}\n" ++
                     cElse
genStmt (While e stmts) = 
            genExpr e           >>= \cE ->
            mapM genStmt stmts  >>= \cStmts ->
            return $ "while (" ++ cE ++ ")\n{\n" ++
                        indent (concat cStmts) ++
                     "}\n"
genStmt (Return e) = 
            genExpr e           >>= \cE ->
            return $ "return " ++ cE ++ ";"
genStmt (Skip) = return "skip;\n"
genStmt (Loop lbl stmts) = mapM genStmt stmts >>= \ cStmts ->
                           return $ "loop " ++ lbl ++ "\n{\n" ++
                                       indent (concat cStmts) ++
                                    "}\n"
genStmt (MatchUnion e alts) = genExpr e >>= \ cE ->
                              mapM genAlt alts >>= \ cAlts ->
                              return $ "match (" ++ cE ++ ")\n{\n" ++
                                          indent (concat cAlts) ++
                                       "}\n"
genStmt (Jump l)       = return $ "jump " ++ l ++ ";\n"

genStmt Break          = return "break;"

genStmt (DeclStmt d)   = genVarDecl d
--genStmt s      = error $ "Can't pretty-print this: " ++ show s

genAlt :: (Pat,[Stmt]) -> M String
genAlt (p,stmts) = genPat p >>= \ cP ->
                   mapM genStmt stmts >>= \ cStmts ->
                   return $ cP ++ "\n{\n" ++
                              indent (concat cStmts) ++
                            "}\n"

genBinder :: PatBinder -> M String
genBinder (VarBinder v)   = return v
genBinder (ConstBinder i) = return (show i)
genBinder WildcardBinder  = return "_"
genBinder _               = return "__PATBINDER"

genPat :: Pat -> M String
genPat (PatMatch ctor binders) = mapM genBinder binders >>= \ cBinders ->
                                 return $ ctor ++ "(" ++ intercalate "," cBinders ++ ")"
genPat (PatTuple binders)      = mapM genBinder binders >>= \ cBinders ->
                                 return $ "mkpair(" ++ intercalate "," cBinders ++ ")"
genPat (PatVar v)              = return v
genPat PatDefault              = return "_"


genHandlerSpec :: HandlerSpec -> M String
genHandlerSpec (Interrupt int) = return $ show int
genHandlerSpec (Trap)          = return "trap"
genHandlerSpec (Init)          = return "init"
genHandlerSpec (Exc)           = return "exception"

genMods :: Modifier -> M String
genMods (Const) = return "const"

genLHS :: LHS -> M String
genLHS (LHSVar s) = return s

--
-- added fixed arrays
--
-- (2010.05.19) Schulz
--
genLHS (LHSVarIX v i) = genExpr i >>= \i' ->
                        return $ v ++ '[':i' ++ "]"

genLHS (LHSMEM e s) = 
            genExpr e       >>= \cE ->
            return $ "MEM[" ++ cE ++ "][" ++ s ++ "]"

genCaseArm :: (CaseSelector,[Stmt]) -> M String
genCaseArm (cs, stmts) = 
            genCaseSelector cs  >>= \cCS ->
            mapM genStmt stmts   >>= \cStmts ->
            return $ cCS ++ " =>\n{\n" ++ 
                        indent (concat cStmts) ++
                    "}\n"

genCaseSelector :: CaseSelector -> M String
genCaseSelector (Default) = return "default:"
genCaseSelector (CaseExpr e) = genExpr e >>= return 

indent :: String -> String
indent  = unlines . map ("   "++) . lines

genExpr :: Expr -> M String
genExpr (Var s) = return s

--
-- static-length arrays
--
-- (2010.05.19) Schulz
genExpr (VarIX s n) = genExpr n >>= \n' ->
                      return $ s ++ ('[':n') ++ "]"

genExpr (LitInt i)    = return $ show i
genExpr (LitBool b)   = return $ show b
genExpr (LitChar c)   = return "\'c\'"
genExpr (LitString s) = return $ '\"':s ++ "\""

genExpr (Add e1 e2) =
            genExpr e1      >>= \cE1 ->
            genExpr e2      >>= \cE2 ->
            return $ "(" ++ cE1 ++ " + " ++ cE2 ++ ")"
genExpr (Sub e1 e2) = 
            genExpr e1      >>= \cE1 ->
            genExpr e2      >>= \cE2 ->
            return $ "(" ++ cE1 ++ " - " ++ cE2 ++ ")"
genExpr (Mul e1 e2) = 
            genExpr e1      >>= \cE1 ->
            genExpr e2      >>= \cE2 ->
            return $ "(" ++ cE1 ++ " * " ++ cE2 ++ ")"
genExpr (Div e1 e2) = 
            genExpr e1      >>= \cE1 ->
            genExpr e2      >>= \cE2 ->
            return $ "(" ++ cE1 ++ " / " ++ cE2 ++ ")"
genExpr (Modulus e1 e2) = 
            genExpr e1      >>= \cE1 ->
            genExpr e2      >>= \cE2 ->
            return $ "(" ++ cE1 ++ " % " ++ cE2 ++ ")"
genExpr (Neg e1) = 
            genExpr e1      >>= \cE1 ->
            return $ "(-" ++ cE1 ++ ")"
genExpr (AndLogic e1 e2) =
            genExpr e1      >>= \cE1 ->
            genExpr e2      >>= \cE2 ->
            return $ "(" ++ cE1 ++ " && " ++ cE2 ++ ")"
genExpr (OrLogic e1 e2)     = 
            genExpr e1      >>= \ cE1 ->
            genExpr e2      >>= \ cE2 ->
            return $ "(" ++ cE1 ++ " || " ++ cE2 ++ ")"
genExpr (Not e) =
            genExpr e       >>= \ cE ->
            return $ "!(" ++ cE ++ ")"
genExpr (IsLT e1 e2) = 
            genExpr e1      >>= \ cE1 ->
            genExpr e2      >>= \ cE2 ->
            return $ "(" ++ cE1 ++ " < " ++ cE2 ++ ")"
genExpr (IsGT e1 e2) =
            genExpr e1      >>= \ cE1 ->
            genExpr e2      >>= \ cE2 ->
            return $ "(" ++ cE1 ++ " > " ++ cE2 ++ ")"
genExpr (IsLTE e1 e2)= 
            genExpr e1      >>= \cE1 ->
            genExpr e2      >>= \cE2 ->
            return $ "(" ++ cE1 ++ " <= " ++ cE2 ++ ")"
genExpr (IsGTE e1 e2) =
            genExpr e1      >>= \cE1 ->
            genExpr e2      >>= \cE2 ->
            return $ "(" ++ cE1 ++ " >= " ++ cE2 ++ ")"
genExpr (IsEq e1 e2) =
            genExpr e1      >>= \ cE1 ->
            genExpr e2      >>= \ cE2 ->
            return $ "(" ++ cE1 ++ " == " ++ cE2 ++ ")"
genExpr (NotEq e1 e2) =
            genExpr e1      >>= \ cE1 ->
            genExpr e2      >>= \ cE2 ->
            return $ "(" ++ cE1 ++ " != " ++ cE2 ++ ")"
genExpr (AndBit e1 e2)= 
            genExpr e1      >>= \ cE1 ->
            genExpr e2      >>= \ cE2 ->
            return $ "(" ++ cE1 ++ " & " ++ cE2 ++ ")"
genExpr (OrBit e1 e2) =
            genExpr e1      >>= \ cE1 ->
            genExpr e2      >>= \ cE2 ->
            return $ "(" ++ cE1 ++ " | " ++ cE2 ++ ")"
genExpr (XorBit e1 e2) =
            genExpr e1      >>= \ cE1 ->
            genExpr e2      >>= \ cE2 ->
            return $ "(" ++ cE1 ++ " ^ " ++ cE2 ++ ")"
genExpr (ShiftL e1 e2) = 
            genExpr e1      >>= \ cE1 ->
            genExpr e2      >>= \ cE2 ->
            return $ "(" ++ cE1 ++ " << " ++ cE2 ++ ")"
genExpr (ShiftR e1 e2) =
            genExpr e1      >>= \ cE1 ->
            genExpr e2      >>= \ cE2 ->
            return $ "(" ++ cE1 ++ " >> " ++ cE2 ++ ")"
genExpr (NotBit e) =
            genExpr e       >>= \ cE ->
            return $ "~(" ++ cE ++ ")"
genExpr (FunCall f es) =
            mapM genExpr es >>= \ cEs ->
            return $ f ++ "(" ++ intercalate ", " cEs ++ ")"
genExpr (MemAccess e1 e2)  = 
            genExpr e1      >>= \ cE1 ->
            genExpr e2      >>= \ cE2 ->
            return $ "MEM[" ++ cE1 ++ "][" ++ cE2 ++ "]"
genExpr (ImageSegCount v)   = 
            return $ v ++ ".segc"
genExpr (ImageSegVAddr v e) = 
            genExpr e       >>= \ cE ->
            return $ v ++ ".segs[" ++  cE ++ "].vaddr"
genExpr (ImageSegPAddr v e) = 
            genExpr e       >>= \ cE ->
            return $ v ++ ".segs[" ++  cE ++ "].paddr"
genExpr (ImageSegAlign v e) = 
            genExpr e       >>= \ cE ->
            return $ v ++ ".segs[" ++ cE ++ "].align"
genExpr (ImageSegSize v e)  = 
            genExpr e       >>= \ cE ->
            return $  v ++ ".segs[" ++ cE ++ "].size"
genExpr (CtorApp ctor es) =
            mapM genExpr es >>= \ cEs ->
            return $ ctor ++ "(" ++ intercalate "," cEs ++ ")"

genExpr (StructMember e f) = genExpr e >>= \e' ->
                             return $
                               '(':e' ++ ')':'.':f

genExpr (UnionMember e f)  = genExpr e >>= \e' ->
                             return $
                               '(':e' ++ ')':'.':f

genExpr (Top e)     = genExpr e >>= \s ->
                      return $ "top(" ++ s ++ ")"

genExpr (SRest e)   = genExpr e >>= \s ->
                      return $ "srest(" ++ s ++ ")"

genExpr (Pop e)     = genExpr e >>= \s ->
                      return $ "pop(" ++ s ++ ")"

genExpr (Push e e') = genExpr e >>= \s ->
                      genExpr e' >>= \s' ->
                      return $ "push(" ++ s ++ ',':s' ++ ")"

genExpr (IsEmpty e) = genExpr e >>= \s ->
                      return $ "__isempty(" ++ s ++ ")"

genExpr EmptyStack = return "NULL"

genExpr (MkPair e1 e2) =
            genExpr e1 >>= \ cE1 ->
            genExpr e2 >>= \ cE2 ->
            return $ "mkpair(" ++ cE1 ++ "," ++ cE2 ++ ")"

genExpr (RunThread e) = genExpr e >>= \s ->
                        return ("__run(" ++ s ++ ")")

genExpr (MkThread stmts) = mapM genStmt stmts >>= \ cStmts ->
                           return $ "mkthread\n{\n" ++
                                    indent (concat cStmts) ++
                                    "}"

genExpr (Slice e)     = genExpr e >>= \s ->
                        return ("__slice(" ++ s ++ ")")

genExpr (IsDone e)    = genExpr e >>= \s ->
                        return ("__isdone(" ++ s ++ ")")

genExpr (TRetOf e)    = genExpr e >>= \s ->
                        return (s ++ ".__ret")

genExpr (TTail e)     = genExpr e >>= \s ->
                        return (s ++ ".__rts")

genExpr (SigOf e)     = genExpr e >>= \s ->
                        return (s ++ ".__sig")


{--

I've just been hacking Codegen/ETICgen.hs, and replacing evalprog with the following code.  Then rungentest will generate "out.etic" for you.  


--andrew--
import ETIC.Print
import ETIC.Template
import Control.Monad.Identity
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
                           --let prog = (Prog (decls ++ [mainfxn]))
                           let prog_decls = Prog decls
                           let prog_fxn = Prog [mainfxn] 
                           liftIOCg $ writeFile "./out.etic" ( 
                                        "/*AUTOGEN*/\n" ++ 
                                        runIdentity( genTimer ) ++ 
                                        runIdentity (genLoadImage "./TestPrograms/hi.elf" 1) ++
                                        runIdentity (genLoadImage "./TestPrograms/lo.elf" 2) ++
                                        runIdentity (genInitImage [1,2] ) ++ 
                                        "/* CT DECLS */\n" ++
                                        runIdentity ( pprint prog_decls) ++ 
                                        "\n/*CT FCTNS*/\n" ++ 
                                        runIdentity (pprint prog_fxn) 
                                      )
                           return ()
--}

