{-# LANGUAGE MultiParamTypeClasses,FunctionalDependencies,FlexibleInstances #-}

--
-- FIXME: This has gotten quite junky and needs extensive cleanup
--

module CT.Parser (parse,dumpHs) where

import CT.Syntax

import Language.Haskell.Syntax
import Language.Haskell.Parser
import IO
import Data.Maybe
import Data.List

parser :: String -> CtsProg
parser = convert . runPR . parseModule

dumpHs :: String -> IO ()
dumpHs file = do
                 h <- openFile file ReadMode
                 contents <- hGetContents h
                 let ast = runPR $ parseModuleWithMode (ParseMode file) $ contents
                 print (show ast)

runPR :: ParseResult a -> a
runPR (ParseOk x)       = x
runPR (ParseFailed l m) = error msg
           where msg = "Error: " ++ m ++ " at " ++ show l

parse :: String -> IO CtsProg
parse file = do
	h <- openFile file ReadMode
	contents <- hGetContents h
	return $ convert $ runPR $ parseModuleWithMode (ParseMode file) $ contents


-- | Things that can be converted from Hs
class FromHs a b | a -> b where
	convert :: a -> b

------------------------- Convert a Module --------------------
deModule :: Module -> String
deModule (Module s) = s

instance FromHs HsModule CtsProg where
	convert (HsModule _ _ _ _ decls) = CtsProg (concatMap convert decls)

deHsName :: HsName -> String
deHsName (HsIdent x)  = x
deHsName (HsSymbol x) = x

instance FromHs SrcLoc CtsSrcPos where
        convert (SrcLoc filename line col) = CtsSrcPos filename line col

unrollLamVars :: HsExp -> ([CtsIdent],HsExp)
unrollLamVars (HsParen e) =
    let
       (vs,body) = unrollLamVars e
    in
       (vs,HsParen body)
unrollLamVars (HsLambda _ [HsPVar (HsIdent v)] body) =
    let
       (vs,body') = unrollLamVars body
    in
       (v:vs,body')
unrollLamVars e = ([],e)

-------------------------  Declarations ------------------------------
--
-- type synonym implementation is anchored here:
-- rather than parsing type synonyms as a separate structure,
-- type synonyms are treated as data declarations with
-- a single constructor whose identifier is the empty string,
--
-- i.e.
--
-- type TypeName = OtherType
--
-- parses as:
--
-- (CtsDataDecl pos TypeName [cdec])
--  where
--    cdec = CtsConDecl "" [OtherType]
--
-- 30.06.09 Schulz
--
instance FromHs HsDecl [CtsDecl] where
{-  ADAM'S VERSION:
        convert (HsTypeDecl pos name vars ty) = if null vars then [CtsTypeDecl (convert pos) (deHsName name) (convert ty)]
                                                             else error "Type decl contains type variables"
-}

        convert (HsTypeDecl pos name vars ty) = if null vars  -- 30.06.09 Schulz
                                                then 
                                                  let cdec = (CtsConDecl "" [(convert ty)])
                                                  in
                                                    [CtsDataDecl (convert pos) (deHsName name) [cdec]]
                                                else error "Type decl contains type variables"
	convert (HsNewTypeDecl _ _ _ _ _ _) = error "HsNewTypeDecl"
	convert (HsClassDecl _ _ _ _ _)     = error "HsClassDecl"
	convert (HsInstDecl _ _ _ _ _)      = error "HsInstDecl"
	convert (HsDefaultDecl _ _)         = error "HsDefaultDecl"

	convert (HsPatBind pos (HsPVar name) rhs whereClauses) = if null whereClauses
                                                                   then [CtsFunDecl (convert pos) (deHsName name) [] (convert (deHsRhs rhs))]
                                                                   else error $ "Pattern bind has where clauses: " ++ show pos

	convert d@(HsPatBind pos _ _ _)     = error $ "HsPatBind: " ++ show pos ++ " --- " ++ show d
	convert (HsInfixDecl _ _ _ _)       = error "HsInfixDecl"

	convert b@(HsFunBind ((HsMatch _ (HsIdent "monad") _ _ _):_)) = mkMonadDecls b

	convert (HsFunBind [HsMatch pos name pats rhs []]) = [CtsFunDecl (convert pos) (deHsName name) (map dePat pats) (convert (deHsRhs rhs))]
	                                                       where
	                                                           dePat (HsPVar n) = deHsName n
                                                                   dePat p          = error $ show pos ++ ": invalid pattern: " ++ show p
	convert b@(HsFunBind _)             = error $ "invalid HsFunBind: " ++ (show b)

	convert (HsTypeSig pos [n] (HsQualType [] t)) = 
                                              [CtsFunTySig (convert pos) (deHsName n) argTys retTy]
                                              where
                                                 tys    = map convert (deFunType t)
                                                 argTys = reverse (drop 1 (reverse tys))
                                                 retTy  = head (reverse tys)

	convert (HsDataDecl pos _ n _ cs _)  = [CtsDataDecl (convert pos) (deHsName n) (map convert cs)]

unfoldLayerExps :: HsExp -> [HsExp]
unfoldLayerExps (HsInfixApp e1 (HsQVarOp (UnQual (HsSymbol "+"))) e2) = (unfoldLayerExps e1) ++ [e2]
unfoldLayerExps e                                                     = [e]

convertTypeExp :: HsExp -> CtsType
convertTypeExp (HsCon (UnQual (HsIdent "Int")))    = TyInt
convertTypeExp (HsCon (UnQual (HsIdent "Bool")))   = TyBool
convertTypeExp (HsCon (UnQual (HsIdent "String"))) = TyString
convertTypeExp (HsCon (UnQual (HsIdent "Memory"))) = TyMemory -- provisional, for defunctionalizer back-end; 24.07.09 Schulz
convertTypeExp (HsCon (UnQual (HsIdent "InPort"))) = TyInPort -- ports types; (2009.12.14) Schulz
convertTypeExp (HsCon (UnQual (HsIdent "OutPort"))) = TyOutPort -- ports types; (2009.12.14) Schulz
convertTypeExp (HsCon (Special HsUnitCon))         = TyUnit
convertTypeExp (HsCon (UnQual (HsIdent "()")))     = TyUnit
convertTypeExp (HsCon (UnQual (HsIdent i)))        = TyADT i
convertTypeExp (HsTuple ts)                        = TyTuple (map convertTypeExp ts)
convertTypeExp e                                   = error ("convertTypeExp: " ++ show e)

convertLayerExp :: HsExp -> CtsMonadLayer
convertLayerExp (HsApp (HsCon (UnQual (HsIdent "ResT"))) (HsCon (UnQual (HsIdent baseMonad)))) =
   CtsResumptionLayer baseMonad
convertLayerExp (HsApp (HsApp (HsCon (UnQual (HsIdent "StateT"))) (HsParen tExpr)) (HsCon (UnQual (HsIdent layerName)))) =
   CtsStateLayer (convertTypeExp tExpr) layerName
convertLayerExp (HsApp (HsApp (HsApp (HsCon (UnQual (HsIdent "ReactT"))) (HsCon (UnQual (HsIdent reqName)))) (HsCon (UnQual (HsIdent rspName)))) (HsCon (UnQual (HsIdent baseMonad)))) =
   CtsReactiveLayer reqName rspName baseMonad
convertLayerExp e = error $ "\nInvalid monad layer: " ++ show e

layersFromRhs :: HsExp -> [CtsMonadLayer]
layersFromRhs rhs = let
                       layerExps = unfoldLayerExps rhs
                    in
                       map convertLayerExp layerExps

mkMonadDecl :: HsMatch -> CtsDecl
mkMonadDecl (HsMatch pos (HsIdent "monad") [HsPApp (UnQual (HsIdent mName)) []] (HsUnGuardedRhs rhs) []) =
     let 
         layers = layersFromRhs rhs
     in
         CtsMonadDecl (convert pos) mName layers

mkMonadDecls :: HsDecl -> [CtsDecl]
mkMonadDecls (HsFunBind matches) = map mkMonadDecl matches

deFunType :: HsType -> [HsType]
deFunType (HsTyFun t1 t2) = t1 : deFunType t2
deFunType t               = [t]

deHsRhs :: HsRhs -> HsExp
deHsRhs (HsUnGuardedRhs e) = e
deHsRhs (HsGuardedRhss  _) = error "HsGuardedRhss"

deHsBangedType :: HsBangType -> HsType
deHsBangedType (HsBangedTy _)       = error "HsBangedTy"
deHsBangedType (HsUnBangedTy htype) = htype

instance FromHs HsConDecl CtsConDecl where
        convert (HsRecDecl _ _ _) = error "HsRecDecl"
        convert (HsConDecl _pos name typeList) = CtsConDecl (deHsName name) (map (convert . deHsBangedType) typeList)

-----------------------------------------------------------------------------------
-- Begin weird stuff to convert curried tycon application -- not sure it's right --
-----------------------------------------------------------------------------------

isValidTyApp :: HsType -> Bool
isValidTyApp (HsTyApp inner@(HsTyApp _ _) _) = isValidTyApp inner
isValidTyApp (HsTyApp (HsTyCon _) _)         = True
isValidTyApp (HsTyApp _ _)                   = False

deCurryTyApp :: HsType -> (CtsIdent,[CtsType])
deCurryTyApp (HsTyApp (HsTyCon v) arg) = (deHsQName v,[convert arg])
deCurryTyApp (HsTyApp inner arg)       = let
                                            (v,args) = deCurryTyApp inner
                                         in
                                            (v,args ++ [convert arg])

convTyApp :: HsType -> CtsType
convTyApp a = if isValidTyApp a
                 then
                    case deCurryTyApp a of
                       ("[]",[t]) -> TyList t
                       (v,[t])    -> TyMonadic v t
                       _          -> error "Too many arguments to type constructor"
                 else error "invalid application"

---------------------
-- End weird stuff --
---------------------

--
-- type synonyms here:
--
-- 24.06.09 Schulz
--
instance FromHs HsType CtsType where
    convert (HsTyFun a b)   = error "HsTyFun"
    convert (HsTyTuple l)   = TyTuple (map convert l)
    convert t@(HsTyApp _ _) = convTyApp t
    convert (HsTyVar name)  = error "HsTyVar"
    convert (HsTyCon name)  = case deHsQName name of
                                 "Int"     -> TyInt
                                 "Bool"    -> TyBool
                                 "String"  -> TyString
                                 "Memory"  -> TyMemory -- 24.07.09 Schulz
                                 "InPort"  -> TyInPort -- (2009.12.14) Schulz
                                 "OutPort" -> TyOutPort -- (2009.12.14) Schulz
                                 "()"      -> TyUnit
                                 n         -> TyADT n

------------------------- Expressions -------------------------
deHsQName :: HsQName -> String
deHsQName (Qual m name)  = (deModule m) ++ "." ++ (deHsName name)
deHsQName (Special t) = pp t -- error "What's a 'special' type?"
  where pp HsUnitCon      = "()"     	-- ^ unit type and data constructor @()@
	pp HsListCon      = "[]"	-- ^ list type constructor @[]@
	pp HsFunCon       = "(->)"	-- ^ function type constructor @->@
	pp (HsTupleCon i) = "("++show i++"-tuple)" -- ^ /n/-ary tuple type 
	pp HsCons	  = ":"                    -- ^ list constructor @(:)@
deHsQName (UnQual name)  = deHsName name


instance FromHs HsLiteral CtsLit where
	convert (HsInt i)        = CtsLitInt (fromInteger i)
	convert (HsChar c)       = error "HsChar"
	convert (HsString s)     = CtsLitString s
	convert (HsFrac r)       = error "HsFrac"
	-- GHC unboxed literals:
	convert (HsCharPrim c)   = error "HsCharPrim"
	convert (HsStringPrim s) = error "HsStringPrim"
	convert (HsIntPrim i)    = error "HsIntPrim"
	convert (HsFloatPrim r)  = error "HsFloatPrim"
	convert (HsDoublePrim r) = error "HsDoublePrim"

deHsQOp :: HsQOp -> String
deHsQOp (HsQVarOp n) = deHsQName n
deHsQOp (HsQConOp n) = deHsQName n

--------------------------------------------------------------------------------------
-- Begin weird stuff to convert curried function application -- not sure it's right --
--------------------------------------------------------------------------------------

isValidApp :: HsExp -> Bool
isValidApp (HsParen e)                 = isValidApp e
isValidApp (HsApp (HsParen (HsApp (HsVar (UnQual (HsIdent "fix"))) _)) _) = True
isValidApp (HsApp (HsApp (HsVar (UnQual (HsIdent "fix"))) _) _) = True
isValidApp (HsApp (HsVar (UnQual (HsIdent "fix"))) _) = True

--
-- validate the semifix syntax (2009.11.09 Schulz)
--

isValidApp (HsApp (HsParen (HsApp (HsApp (HsVar (UnQual (HsIdent "semifix"))) _) _)) _) = True
isValidApp (HsApp (HsApp (HsVar (UnQual (HsIdent "semifix"))) _) _) = True
isValidApp (HsApp (HsVar (UnQual (HsIdent "semifix"))) _) = True

--
-- end change
--

isValidApp (HsApp inner@(HsApp _ _) _) = isValidApp inner
isValidApp (HsApp (HsVar _) _)         = True
isValidApp (HsApp (HsCon _) _)         = True
isValidApp (HsApp _ _)                 = False

deCurryApp :: HsExp -> CtsExpr
deCurryApp (HsParen e)           = deCurryApp e
deCurryApp (HsApp (HsApp (HsVar (UnQual (HsIdent "fix"))) lam) arg) =
                                   let
                                      (lamVars,body) = unrollLamVars lam
                                   in
                                      (CtsFixApp lamVars (convert body) [convert arg] noType)

--
-- case(s) for the conditional-fix; put here 2009.11.05 Schulz
--
deCurryApp (HsApp (HsApp (HsApp (HsVar (UnQual (HsIdent "semifix"))) sent) lam) arg) =
                                   let
                                      (lamVars,body) = unrollLamVars lam
                                   in
                                      (CtsSemiFixApp (convert sent) lamVars (convert body) [convert arg] noType)

deCurryApp (HsApp (HsParen (HsApp (HsApp (HsVar (UnQual (HsIdent "semifix"))) sent) lam)) arg) =
                                   let
                                      (lamVars,body) = unrollLamVars lam
                                   in
                                      (CtsSemiFixApp (convert sent) lamVars (convert body) [convert arg] noType)

deCurryApp (HsApp (HsApp (HsVar (UnQual (HsIdent "semifix"))) sent) lam) =
				   let
				      (lamVars,body) = unrollLamVars lam
				   in
				      (CtsSemiFixApp (convert sent) lamVars (convert body) [] noType)
--
--
deCurryApp (HsApp (HsParen (HsApp (HsVar (UnQual (HsIdent "fix"))) lam)) arg) =
                                   let
                                      (lamVars,body) = unrollLamVars lam
                                   in
                                      (CtsFixApp lamVars (convert body) [convert arg] noType)
deCurryApp (HsApp (HsVar (UnQual (HsIdent "fix"))) lam) =
				   let
				      (lamVars,body) = unrollLamVars lam
				   in
				      (CtsFixApp lamVars (convert body) [] noType)
deCurryApp (HsApp (HsVar v) arg) = CtsApp (deHsQName v) [convert arg] noType
deCurryApp (HsApp (HsCon v) arg) = CtsConstrApp (deHsQName v) [convert arg] noType
deCurryApp (HsApp inner arg)     = case deCurryApp inner of
                                      (CtsConstrApp v args _)    -> CtsConstrApp v (args ++ [convert arg]) noType
                                      (CtsFixApp vs body args _) -> CtsFixApp vs body (args ++ [convert arg]) noType
                                      (CtsSemiFixApp sent vs body args _) -> CtsSemiFixApp sent vs body (args ++ [convert arg]) noType
                                      (CtsApp v args _)          -> CtsApp v (args ++ [convert arg]) noType

convApp :: HsExp -> CtsExpr
convApp a = if isValidApp a then deCurryApp a else error $ "invalid application:\n" ++ (show a)

---------------------
-- End weird stuff --
---------------------

instance FromHs HsExp CtsExpr where
	-- We only handle lambdas in the context of binds and fix -- so these
	-- patterns are pretty hairy
	
	-- Monad stuff
	convert (HsInfixApp e1 (HsQVarOp (UnQual (HsSymbol ">>="))) (HsLambda _ [HsPVar (HsIdent v)] e2)) =
	                        CtsBind (convert e1) v (convert e2) noType
	convert (HsInfixApp e1 (HsQVarOp (UnQual (HsSymbol "||="))) (HsLambda _ [HsPVar (HsIdent v)] e2)) =
	                        CtsBind (convert e1) v (convert e2) noType
	convert (HsInfixApp e1 (HsQVarOp (UnQual (HsSymbol "*="))) (HsLambda _ [HsPVar (HsIdent v)] e2)) =
	                        CtsBind (convert e1) v (convert e2) noType
	                        
	convert (HsInfixApp e1 (HsQVarOp (UnQual (HsSymbol ">>"))) e2) =
	                        CtsBindNull (convert e1) (convert e2) noType
	convert (HsApp (HsVar (UnQual (HsIdent "return"))) e) =
	                        CtsReturn (convert e) noType

        --
        -- The rest
        --
        convert (HsLit l)     = CtsLitExpr (convert l) noType
        convert (HsNegApp e)  = CtsNeg (convert e) noType
	convert (HsInfixApp a op b) = CtsInfixApp (convert a) (deHsQOp op) (convert b) noType
        convert a@(HsApp _ _) = convApp a
        convert (HsTuple es)  = CtsTuple (map convert es) noType
        convert (HsList [])   = error "Empty lists must be explicitly typed"
	convert (HsList es)   = CtsList (map convert es) noType
        convert (HsVar name)  = CtsVar (deHsQName name) noType
        convert (HsIf c t f)  = CtsIfThenElse (convert c) (convert t) (convert f) noType
        convert (HsParen e)   = convert e
	convert (HsLambda pos _ _) = error $ show pos ++ ": lambda expressions are only allowed in fix and bind"
        convert (HsExpTypeSig _ (HsList []) (HsQualType [] t)) = CtsEmptyList (convert t)

        convert (HsCon (UnQual (HsIdent "True"))) = CtsLitExpr (CtsLitBool True) noType
        convert (HsCon (UnQual (HsIdent "False"))) = CtsLitExpr (CtsLitBool False) noType
        convert (HsCon (Special HsUnitCon))      = CtsUnit noType
        convert (HsCon (UnQual (HsIdent ident))) = CtsConstrApp ident [] noType

	convert (HsCase cond altList) = CtsCase (convert cond) (map convert altList) noType

	convert (HsDo _)                         = error "HsDo"
	convert (HsLeftSection _ _)              = error "HsLeftSection"
	convert (HsRightSection _ _)             = error "HsRightSection"
	convert (HsRecConstr _ _)                = error "HsRecConstr"
	convert (HsRecUpdate _ _)                = error "HsRecUpdate"
	convert (HsEnumFrom e)                   = error "HsEnumFrom"
	convert (HsEnumFromTo from to)           = error "HsEnumFromTo"
	convert (HsEnumFromThen from thenE)      = error "HsEnumFromThen"
	convert (HsEnumFromThenTo from thenE to) = error "HsEnumFromThenTo"
	convert (HsListComp e stmtList)          = error "HsListComp"
	convert (HsExpTypeSig _pos e ty)         = error "HsExpTypeSig"
	convert (HsAsPat name e)                 = error "HsAsPat"
	convert HsWildCard                       = error "HsWildCard"
	convert (HsIrrPat e)                     = error "HsIrrPat"

        convert e                                = error $ "can't convert: " ++ (show e)
        
--	convert (HsLet declList letBody) = CtLet (map convert declList) (convert letBody)

------------------------- Patterns -----------------------------
extractName :: HsPat -> CtsIdent
extractName (HsPVar name) = deHsName name
extractName n             = error $ "Can't extract name: " ++ show n

instance FromHs HsPat CtsPat where
	convert (HsPVar name)                   = error "HsPVar"
	convert (HsPLit lit)                    = error "HsPLit"
	convert (HsPNeg p)                      = error "HsPNeg"
	convert (HsPInfixApp a op b)            = CtsPInfixApp (CtsInfixPat $ deHsQName op)
                                                                 (extractName a) (extractName b)
--	convert (HsPInfixApp a op b)            = error "HsPInfixApp"
	convert (HsPApp n ps)                   = CtsPConstr (deHsQName n) (map extractName ps)
	convert (HsPTuple ps)                   = CtsPTuple (map extractName ps)
	convert (HsPList ps)                    = error "HsPList"
	convert (HsPParen p)                    = convert p
	convert (HsPRec c fields)               = error "HsPRec"
	-- special case that would otherwise be buggy
	convert (HsPAsPat name (HsPIrrPat pat)) = error "HsPAsPat-HsPIrrPat"
	convert (HsPAsPat name pat)             = error "HsAsPat"
	convert HsPWildCard                     = CtsPWildCard -- added 03.07.09 Schulz
--	convert HsPWildCard                     = error "HsPWildCard"
	convert (HsPIrrPat pat)                 = error "HsPIrrPat"


deHsGuardedAlts :: HsGuardedAlts -> HsExp
deHsGuardedAlts (HsUnGuardedAlt e) = e
deHsGuardedAlts (HsGuardedAlts _)  = error "HsGuardedAlts"

------------------------- Case bodies  -------------------------
instance FromHs HsAlt CtsAlt where
	convert (HsAlt _ pat gAlts []) = CtsAlt (convert pat) (convert . deHsGuardedAlts $ gAlts)
