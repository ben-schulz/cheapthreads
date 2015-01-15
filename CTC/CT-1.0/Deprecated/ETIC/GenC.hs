module Deprecated.ETIC.GenC where

import Deprecated.ETIC.Syntax
import Data.List
import Data.Maybe
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Reader

type M = ReaderT Env (StateT Int Identity)
runM m = fst (runIdentity (runStateT (runReaderT m []) 0) )

type Env = [TopDecl]

{-- 
 --envionment functions
 --}
 
--
tryToGetArgTypes :: String -> TopDecl -> Maybe [Type]
tryToGetArgTypes ctor (UnionDecl _ cases) = lookup ctor cases
tryToGetArgTypes _    _                   = Nothing

--
lookupCtorArgTypes :: Env -> String -> [Type]
lookupCtorArgTypes env ctor = case msum (map (tryToGetArgTypes ctor) env) of
                                (Just tys) -> tys
                                Nothing    -> error $ "Undefined constructor " ++ ctor

-- returns: (union name, construct name)  OR nothing
tryToGetCtorNameUnionCase :: String -> String -> (String,[Type]) -> Maybe (String,String)
tryToGetCtorNameUnionCase ctor uname (name,_) = if ctor == name
                                             then Just (uname,name)
                                             else Nothing

-- returns (union name, constructor name) OR nothing
tryToGetCtorName :: String -> TopDecl -> Maybe (String,String)
tryToGetCtorName func (UnionDecl uname cases) = msum ( map (tryToGetCtorNameUnionCase func uname) cases) 
tryToGetCtorName _ _                    = Nothing

 -- returns: (union name, construct name) OR nothing 
lookupCtorName :: Env -> String -> Maybe (String,String)
lookupCtorName env func = msum ( map (tryToGetCtorName func) env)

 -- 
tryToGetCtorIDUnionCase :: String -> ((String,[Type]),Int) -> Maybe Int
tryToGetCtorIDUnionCase ctor ((name,_),id)  = if ctor == name
                                              then Just id
                                              else Nothing

 --
tryToGetCtorID :: String -> TopDecl -> Maybe Int
tryToGetCtorID func (UnionDecl uname cases) = msum ( map ( tryToGetCtorIDUnionCase func) (zip cases [0..]) )
tryToGetCtorID _ _                          = Nothing

 --
lookupCtorID :: Env -> String -> Maybe Int
lookupCtorID env func = msum ( map ( tryToGetCtorID func) env)

{--
 -- state functions 
 --}

genVar :: M String 
genVar = get    >>= \ cInt ->
         put (cInt+1) >>  
         ( return $ "m_" ++ show cInt )




{-----------------------------------------
 --
 --
 -- Generate dynamic boilerplate.
 --
 --
 -------------------------------------------
 --}
genBP :: Prog -> M String
genBP (Prog ds) =
       mapM genIODef ds          >>= \cIODefs ->
       mapM genUnions ds         >>= \cUnions ->
       mapM genPrototype ds      >>= \ cProtos ->
       mapM genHandlerInstall ds >>= \ cInstalls ->
       return $ "#include \"static_bp.h\"\n" ++
                concat cIODefs ++ "\n" ++
                concat cUnions ++ "\n" ++
                concat cProtos ++ "\n" ++
                "void bp_init_dynamic()\n" ++
                "{\n" ++
                indent (concat cInstalls) ++
                "}\n" 
{--
 -- Generate IO declarations
 --}
genIODef :: TopDecl -> M String
genIODef (IODecl ty name add) = 
        genTy ty >>= \ (cTy, cTyP) ->
        return $ "volatile " ++ cTy ++ " *" ++ name ++ cTyP ++  " = (" ++ cTy ++ " *) " ++ show add ++ "UL;\n"
genIODef _                    = return ""

{--
 -- Generate Union declarations
 --}
genUnions :: TopDecl -> M String
genUnions ( UnionDecl name members) = 
                                    mapM genUnionMember members            >>= \ cMembers ->
                                    return $ "struct " ++ name ++ "{\n" ++
                                            indent "unsigned int tag;\n" ++
                                            indent "union {\n" ++
                                            indent (indent (concat cMembers)) ++
                                            indent "} u;\n" ++
                                            "};\n" 
genUnions _                                 = return ""

genUnionMember :: (String,[Type]) -> M String
genUnionMember (s,tys) =   mapM genTy tys >>= \ res ->
                           let
                              cTys   = map fst res
                              cTyPs  = map snd res
                              cNames = map (("member_"++) . show) [0..length tys - 1]
                           in return $ "struct " ++ "{\n" ++ 
                                       indent (concat (zipWith3 (\ ty tyP name -> ty ++ " " ++ name ++ tyP ++ ";\n") cTys cTyPs cNames) ) ++
                                       "} " ++ s ++ ";\n"


{--
 -- Generate C function prototypes 
 --}
genPrototype :: TopDecl -> M String
genPrototype (TopVarDecl vd)                 = genVarDecl vd
genPrototype (FunDecl mTy name params locals stmts) =
       genMTy mTy           >>= \ (cMTy, cMTyP) ->
       mapM genParam params >>= \ cParams ->
       return $ cMTy ++ " " ++ name ++ cMTyP  ++ "(" ++ intercalate ", " cParams ++ ");\n"
genPrototype (HandlerDecl (Interrupt i) _ _) = return $ "void handler_int" ++ show i ++ "(void);\n"
genPrototype (HandlerDecl Trap _ _)          = return $ "void handler_trap(void);\n"
genPrototype (HandlerDecl Init _ _)          = return $ "void handler_init(void);\n"
genPrototype (HandlerDecl Exc _ _)           = return $ "void handler_exception(void);\n"
genPrototype (ImageDecl n _)                 = return $ "extern int32_t __" ++ n ++ "_segment_count;\n" ++
                                                        "extern uint32_t *__" ++ n ++ "_segment_vaddrs[];\n" ++
                                                        "extern uint32_t *__" ++ n ++ "_segment_paddrs[];\n" ++
                                                        "extern uint32_t __" ++ n ++ "_segment_sizes[];\n"
genPrototype _                               = return ""

{--
 -- Generate handler() initializations
 --}
genHandlerInstall :: TopDecl -> M String
genHandlerInstall (HandlerDecl (Interrupt i) _ _) = return $ "register_handler_interrupt(" ++ show i ++ ",&handler_int" ++ show i ++ ");\n"
genHandlerInstall (HandlerDecl Trap _ _)          = return $ "register_handler_trap(&handler_trap);\n"
genHandlerInstall (HandlerDecl Init _ _)          = return $ "register_handler_init(&handler_init);\n"
genHandlerInstall (HandlerDecl Exc _ _)           = return $ "register_handler_exception(&handler_exception);\n"
genHandlerInstall _                               = return ""



{----------------------------------------
 --
 --
 -- Generate the main kernel program.
 --
 --
 ----------------------------------------
 --}
genC :: Prog -> M String
genC (Prog ds) = local (const initEnv) (genTopDecls ds)
                where
                  initEnv = catMaybes (map extractUnionDecl ds)
                  extractUnionDecl d@(UnionDecl _ _) = Just d
                  extractUnionDecl _                 = Nothing
                  

genTopDecls :: [TopDecl] -> M String
genTopDecls ds = mapM genTopDecl ds >>= return . concat

genTopDecl :: TopDecl -> M String
genTopDecl (TopVarDecl vd)       = return "" -- This is handled in genPrototype
genTopDecl (IODecl mTy name add) = return ""
genTopDecl (ImageDecl _ _)       = return ""
genTopDecl (FunDecl mTy name params locals stmts) =
       genMTy mTy             >>= \ (cMTy, cMTyP) ->
       mapM genParam params   >>= \ cParams ->
       mapM genVarDecl locals >>= \ cLocals ->
       mapM genStmt stmts     >>= \ cStmts ->
       return $ cMTy ++ " " ++ name ++ cMTyP ++ "(" ++ intercalate ", " cParams ++ ")\n" ++
                "{\n" ++
                indent (concat cLocals) ++
                indent (concat cStmts) ++
                "}\n"
genTopDecl (HandlerDecl (Interrupt i) locals stmts) =
       mapM genVarDecl locals >>= \ cLocals ->
       mapM genStmt stmts     >>= \ cStmts ->
       return $ "void handler_int" ++ show i ++ "()\n" ++
                "{\n" ++
                indent (concat cLocals) ++
                indent (concat cStmts) ++
                "}\n"
genTopDecl (HandlerDecl Trap locals stmts) =
       mapM genVarDecl locals >>= \ cLocals ->
       mapM genStmt stmts     >>= \ cStmts ->
       return $ "void handler_trap()\n" ++
                "{\n" ++
                indent (concat cLocals) ++
                indent (concat cStmts) ++
                "}\n"
genTopDecl (HandlerDecl Init locals stmts) =
       mapM genVarDecl locals >>= \ cLocals ->
       mapM genStmt stmts     >>= \ cStmts ->
       return $ "void handler_init()\n" ++
                "{\n" ++
                indent (concat cLocals) ++
                indent (concat cStmts) ++
                "}\n"
genTopDecl (HandlerDecl Exc locals stmts) =
       mapM genVarDecl locals >>= \ cLocals ->
       mapM genStmt stmts     >>= \ cStmts ->
       return $ "void handler_exception()\n" ++
                "{\n" ++
                indent (concat cLocals) ++
                indent (concat cStmts) ++
                "}\n"

genMTy :: Maybe Type -> M (String, String)
genMTy Nothing  = return ("void","" )
genMTy (Just t) = genTy t

genTy :: Type -> M (String, String)
genTy TyInt         = return ("int", "")
genTy TyByte        = return ("unsigned char", "")
genTy TyBool        = return ("unsigned char", "")
genTy TyChar        = return ("char", "")
genTy TyString      = return ("char*","")
genTy (TyPair ty1 ty2) = return ("typair","")
genTy (TyArray num ty) = genTy ty >>= \(ty,pty) ->
                         return ("tyArray" ,"" )
genTy (TyQueue ty)  = return ("tyqueue","")
genTy (TyStack ty)  = return ("tyStack","")
genTy (TyUnion str) = return ("unionty","")
genTy TyTCB         = return ("tyTCB", "")
genTy (TyUserDef str) = return ("userdef","")
genTy (TyVoid)      = return ("void","")

genVarDecl :: VarDecl -> M String
-- FIXME: this case is a bit hacky
genVarDecl (VarDecl [Const] TyInt name (Just init)) = genExpr init >>= \ (cPre,cInit) ->
                                               return $ cPre ++ "#define " ++ name ++ " (" ++ cInit ++ ")\n"
genVarDecl (VarDecl mods (TyQueue TyInt) name _)    = return $ "struct intQueue " ++ name ++ "Mem = {{0},0,0};\n" ++
                                                               "intQ " ++ name ++ " = &" ++ name ++ "Mem;\n"
genVarDecl (VarDecl mods ty name init) = mapM genModifier mods >>= \ cMods ->
                                         genTy ty              >>= \ (cTy, cTyP) ->
                                         (case init of
                                            Nothing  -> return ""
                                            (Just e) -> genExpr e >>= \ (cPre,cInit) -> return $(" = "++ cInit)) >>= \ cInit -> --FIXME cPre?
                                         return $ concatMap (++" ") cMods ++ cTy ++ " " ++ name ++ cTyP ++ cInit ++ ";\n"

genParam :: (Type,String) -> M String
genParam (ty,name) = genTy ty >>= \ (cTy, cTyP) ->
                     return (cTy ++ " " ++ name ++ cTyP)

genCaseSelector :: CaseSelector -> M String
genCaseSelector Default      = return "default"
genCaseSelector (CaseExpr e) = genExpr e >>= \ (cPre,cExpr) ->
                                        return $ cPre ++ ("case "++cExpr)

genCaseArm :: (CaseSelector,[Stmt]) -> M String
genCaseArm (c,ss) = genCaseSelector c >>= \ cC ->
                    mapM genStmt ss   >>= \ cSs ->
                    return $ cC ++ ":\n" ++ indent (concat (cSs ++ ["break;\n"]))


genLHS :: LHS -> M String
genLHS (LHSVar v)     = return v
genLHS (LHSMEM e r)   = genExpr e >>= \ (cPre,cE) ->
                        return $ cPre ++ " *((uint32_t*)mm_resolve(" ++ cE ++ "," ++ r ++ "))"

{--
 -- generate a statement
 --}
genStmt :: Stmt -> M String
genStmt (ExprStmt e)   = genExpr e >>= \ (cPre,cE) -> 
                         return $ cPre ++ cE ++ ";\n"
genStmt (DeclStmt vD)  = return "" --fixme
genStmt (Assign lhs e) = genLHS lhs >>= \ cLHS ->
                         genExpr e  >>= \ (cPre,cE) -> 
                         return $ cPre ++ cLHS ++ " = " ++ cE ++ ";\n" 
genStmt (SysCall e)    = return "" -- fixme
genStmt (IOStmt s e)   = genExpr e >>= \ (cPre,cE) -> 
                         return $ cPre ++ "*" ++ s ++ " = " ++  cE ++ ";\n"
genStmt (Case e cs)    = genExpr e >>= \ (cPre,cE) ->
                         mapM genCaseArm cs >>= \ cCS ->
                         return $ cPre ++ 
                                  "switch(" ++ cE ++ ")\n" ++
                                  "{\n" ++
                                  indent (concat cCS)  ++
                                  "}\n"
genStmt (IfThenElse e ssT mSsF) =
                         genExpr e        >>= \ (cPre,cE) ->
                         mapM genStmt ssT >>= \ cSsT ->
                         (case mSsF of
                             Nothing    -> return ""
                             (Just ssF) -> mapM genStmt ssF >>= \ cSsF ->
                                           return $ "else\n" ++
                                                    "{\n" ++
                                                    indent (concat cSsF) ++
                                                    "}\n"
                         )                >>= \ cElse ->
                         return $ cPre ++
                                  "if (" ++ cE ++ ")\n" ++
                                  "{\n" ++
                                  indent (concat cSsT) ++
                                  "}\n" ++
                                  cElse
genStmt (While e ssT)  = genExpr e        >>= \ (cPre,cE) ->
                         mapM genStmt ssT >>= \ cSsT ->
                         return $ cPre ++
                                  "while(" ++ cE ++ ")\n" ++
                                  "{\n" ++
                                  indent (concat cSsT) ++
                                  "}\n"

genStmt (Loop e ssT)   = return "_LOOP" --Fixme
genStmt (Jump s)       = return $ "goto " ++ (show s) ++ ";\n"
genStmt (Return e)     = genExpr e >>= \ (cPre,cE) ->
                         return $ cPre ++ "return " ++ cE ++ ";\n"
genStmt Skip           = return "asm volatile (\"nop\");\n"

genModifier :: Modifier -> M String
genModifier Const = return "const"


{--
 String: preamble
 String: expression code
--}
genExpr :: Expr -> M (String,String)
genExpr (Var "errno")       = return ("","_etic_errno")
genExpr (Var v)             = return ("",v)
genExpr (VarIX str e)       = genExpr e >>= \(cPre, cE) ->
                              return ("","")
genExpr (LitInt n)          = return ("",show n)
genExpr (LitBool True)      = return ("","1")
genExpr (LitBool False)     = return ("","0")
genExpr (LitChar e   )      = return ("", show e)
genExpr (LitString e )      = return ("", show e)
genExpr (Add e1 e2)         = genExpr e1 >>= \ (cPre1,cE1) ->
                              genExpr e2 >>= \ (cPre2,cE2) ->
                              return (cPre1 ++ cPre2,"(" ++ cE1 ++ " + " ++ cE2 ++ ")")
genExpr (Sub e1 e2)         = genExpr e1 >>= \ (cPre1,cE1) ->
                              genExpr e2 >>= \ (cPre2,cE2) ->
                              return (cPre1 ++ cPre2,"(" ++ cE1 ++ " - " ++ cE2 ++ ")")
genExpr (Mul e1 e2)         = genExpr e1 >>= \ (cPre1,cE1) ->
                              genExpr e2 >>= \ (cPre2,cE2) ->
                              return (cPre1 ++ cPre2,"(" ++ cE1 ++ " * " ++ cE2 ++ ")")
genExpr (Div e1 e2)         = genExpr e1 >>= \ (cPre1,cE1) ->
                              genExpr e2 >>= \ (cPre2,cE2) ->
                              return (cPre1 ++ cPre2,"(" ++ cE1 ++ " / " ++ cE2 ++ ")")
genExpr (Modulus e1 e2)     = genExpr e1 >>= \ (cPre1,cE1) ->
                              genExpr e2 >>= \ (cPre2,cE2) ->
                              return (cPre1 ++ cPre2,"(" ++ cE1 ++ " % " ++ cE2 ++ ")")
genExpr (Neg e1)            = genExpr e1 >>= \ (cPre1,cE1) -> 
                              return (cPre1,"(-" ++ cE1 ++ ")")
genExpr (AndLogic e1 e2)    = genExpr e1 >>= \ (cPre1,cE1) ->
                              genExpr e2 >>= \ (cPre2,cE2) ->
                              return (cPre1 ++ cPre2,"(" ++ cE1 ++ " && " ++ cE2 ++ ")")
genExpr (OrLogic e1 e2)     = genExpr e1 >>= \ (cPre1,cE1) ->
                              genExpr e2 >>= \ (cPre2,cE2) ->
                              return (cPre1 ++ cPre2,"(" ++ cE1 ++ " || " ++ cE2 ++ ")")
genExpr (Not e)             = genExpr e >>= \ (_,cE) ->
                              return ("","!(" ++ cE ++ ")")
genExpr (IsLT e1 e2)        = genExpr e1 >>= \ (cPre1,cE1) ->
                              genExpr e2 >>= \ (cPre2,cE2) ->
                              return (cPre1 ++ cPre2,"(" ++ cE1 ++ " < " ++ cE2 ++ ")")
genExpr (IsGT e1 e2)        = genExpr e1 >>= \ (cPre1,cE1) ->
                              genExpr e2 >>= \ (cPre2,cE2) ->
                              return (cPre1 ++ cPre2,"(" ++ cE1 ++ " > " ++ cE2 ++ ")")
genExpr (IsLTE e1 e2)       = genExpr e1 >>= \ (cPre1,cE1) ->
                              genExpr e2 >>= \ (cPre2,cE2) ->
                              return (cPre1 ++ cPre2,"(" ++ cE1 ++ " <= " ++ cE2 ++ ")")
genExpr (IsGTE e1 e2)       = genExpr e1 >>= \ (cPre1,cE1) ->
                              genExpr e2 >>= \ (cPre2,cE2) ->
                              return (cPre1 ++ cPre2,"(" ++ cE1 ++ " >= " ++ cE2 ++ ")")
genExpr (IsEq e1 e2)        = genExpr e1 >>= \ (cPre1,cE1) ->
                              genExpr e2 >>= \ (cPre2,cE2) ->
                              return (cPre1 ++ cPre2,"(" ++ cE1 ++ " == " ++ cE2 ++ ")")
genExpr (NotEq e1 e2)       = genExpr e1 >>= \ (cPre1,cE1) ->
                              genExpr e2 >>= \ (cPre2,cE2) ->
                              return (cPre1 ++ cPre2,"(" ++ cE1 ++ " != " ++ cE2 ++ ")")
genExpr (AndBit e1 e2)      = genExpr e1 >>= \ (cPre1,cE1) ->
                              genExpr e2 >>= \ (cPre2,cE2) ->
                              return (cPre1 ++ cPre2,"(" ++ cE1 ++ " & " ++ cE2 ++ ")")
genExpr (OrBit e1 e2)       = genExpr e1 >>= \ (cPre1,cE1) ->
                              genExpr e2 >>= \ (cPre2,cE2) ->
                              return (cPre1 ++ cPre2,"(" ++ cE1 ++ " | " ++ cE2 ++ ")")
genExpr (XorBit e1 e2)      = genExpr e1 >>= \ (cPre1,cE1) ->
                              genExpr e2 >>= \ (cPre2,cE2) ->
                              return (cPre1 ++ cPre2,"(" ++ cE1 ++ " ^ " ++ cE2 ++ ")")
genExpr (ShiftL e1 e2)      = genExpr e1 >>= \ (cPre1,cE1) ->
                              genExpr e2 >>= \ (cPre2,cE2) ->
                              return (cPre1 ++ cPre2,"(" ++ cE1 ++ " << " ++ cE2 ++ ")")
genExpr (ShiftR e1 e2)      = genExpr e1 >>= \ (cPre1,cE1) ->
                              genExpr e2 >>= \ (cPre2,cE2) ->
                              return (cPre1 ++ cPre2,"(" ++ cE1 ++ " >> " ++ cE2 ++ ")")
genExpr (NotBit e)          = genExpr e >>= \ (cPre,cE) ->
                              return (cPre, "~(" ++ cE ++ ")")
genExpr (FunCall f es)      = ask             >>= \ env -> 
                              mapM genExpr es >>= \ results ->
                              genVar          >>= \ tmpVar ->
                              let cEs          = map snd results
                                  preambles     = map fst results
                                  mUnionCtor   = lookupCtorName env f
                              in 
                                case mUnionCtor of
                                    (Just (uname,ctor)) -> 
                                        let  cID        = lookupCtorID env f
                                             varAssigns = zipWith (\x y -> ".u." ++ f ++ ".member_" ++ show x ++ " = " ++ y) [0..] cEs  
                                        in
                                            case cID of 
                                                (Just id) -> 
                                                    return (
                                                       concat preambles ++
                                                        "struct " ++ uname ++ " " ++ tmpVar ++ " = {" ++ 
                                                        ".tag=" ++ show id ++ ", " ++ 
                                                        intercalate ", " varAssigns ++ 
                                                        "};\n",
                                                        tmpVar
                                                    )
                                                Nothing   -> error "no cID for the constructor?!?!?! Thats bad..."
                                    Nothing              -> return (concat preambles,f ++ "(" ++ intercalate ", " cEs ++ ")")
genExpr (TCBAccess e str)   = return ("","") 
genExpr (MemAccess e1 e2)   = genExpr e1 >>= \ (cPre1,cE1) ->
                              genExpr e2 >>= \ (cPre2,cE2) ->
                              return (cPre1 ++ cPre2," * ((uint32_t*) mm_resolve(" ++ cE1 ++ "," ++ cE2 ++ ")) ")
genExpr (ImageSegCount v)   = return ("","__" ++ v ++ "_segment_count")
genExpr (ImageSegVAddr v e) = genExpr e >>= \ (cPre,cE) ->
                              return (cPre,"__" ++ v ++ "_segment_vaddrs[" ++  cE ++ "]")
genExpr (ImageSegPAddr v e) = genExpr e >>= \ (cPre,cE) ->
                              return (cPre,"__" ++ v ++ "_segment_paddrs[" ++  cE ++ "]")
genExpr (ImageSegAlign v e) = genExpr e >>= \ (cPre,cE) ->
                              return (cPre,"__" ++ v ++ "_segment_aligns[" ++ cE ++ "]")
genExpr (ImageSegSize v e)  = genExpr e >>= \ (cPre,cE) ->
                              return (cPre,"__" ++ v ++ "_segment_sizes[" ++ cE ++ "]")
genExpr (CtorApp str es)    = return ("","")
genExpr (StructMember e str) =  genExpr e >>= \ (cPre, cE) ->
                                return ("", cE ++ "." ++ (show str))
genExpr (UnionMember e str) = genExpr e >>= \ (cPre, cE) ->               
                              return ("", cE ++ "." ++ (show str))
genExpr (MkPair e1 e2)      = genExpr e1 >>= \ (cPre1, cE1) ->
                              genExpr e2 >>= \ (cPre2, cE2) ->
                              return ("", "_MkPair")          -- what are the types
genExpr EmptyStack          = return ("", "_Empty_the_Stack_") 
genExpr (IsEmpty e1)        = return ("", "_Is_Stack_Empty_") 
genExpr (Top e)             = return ("", "_get_top_ofstack_nondest_")
genExpr (SRest e)           = return ("", "_get_bottom_ofstack_nondest_")
genExpr (Pop e)             = return ("", "_popoff_stackinoff_ ")
genExpr (Push e1 e2)        = return ("", "_push_oldschool_") 
genExpr (MkThread lstmt)    = return ("", "_nitting_with_kyancy_")
genExpr (RunThread e)       = return ("", "_the_blanket_is_in_the_wind_")
genExpr (Slice e)           = return ("", "_Slice_here_")
genExpr (IsDone e)          = return ("", "_IsDone?_")
genExpr (TRetOf e)          = return ("","")
genExpr (TTail e)           = return ("", "_TTail_")
genExpr (SigOf e)           = return ("", "_SigOf_")
          
indent :: String -> String
indent = unlines . map ('\t':) . lines
