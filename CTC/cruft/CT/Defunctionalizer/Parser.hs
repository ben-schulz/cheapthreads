{-# LANGUAGE MultiParamTypeClasses,FunctionalDependencies #-}

module Parser (
	parser
) where

import Syntax

import Language.Haskell.Syntax
import Language.Haskell.Parser
import IO


parser :: String -> CtModule
parser = convert . runPR . parseModule


runPR :: ParseResult a -> a
runPR (ParseOk x)       = x
runPR (ParseFailed l m) = error msg
           where msg = "Error: " ++ m ++ " at " ++ show l



parseCt :: String -> IO ()
parseCt file = do
	h <- openFile file ReadMode
	contents <- hGetContents h
	putStrLn . show . convert . runPR . parseModule $ contents
	
		
parseHaskell :: String -> IO ()
parseHaskell file = do
	h <- openFile file ReadMode
	contents <- hGetContents h
	putStrLn . show . runPR . parseModule $ contents


		
-- | Things that can be converted to cheap threads
class HsToCt a b | a -> b where
	convert :: a -> b

------------------------- Convert a Module --------------------
deModule :: Module -> String
deModule (Module s) = s

instance HsToCt HsModule CtModule where
	convert (HsModule pos m mbExports imp decls) = CtModule (srcLine pos) (deModule m) (map convert decls)

{- 
--------------------------  Module Header ------------------------------
instance HsToCt HsExportSpec where
	convert (HsEVar name)		     = undefined
	convert (HsEAbs name)		     = undefined
	convert (HsEThingAll name)	     = undefined
	convert (HsEThingWith name nameList) = undefined
	convert (HsEModuleContents m)        = undefined

instance HsToCt HsImportDecl where
	convert (HsImportDecl pos m qual mbName mbSpecs) = undefined

instance HsToCt HsImportSpec where
	convert (HsIVar name)                = undefined
	convert (HsIAbs name)                = undefined
	convert (HsIThingAll name)           = undefined
	convert (HsIThingWith name nameList) = undefined
-}	

deHsName :: HsName -> String
deHsName (HsIdent x)  = x
deHsName (HsSymbol x) = x

deHsNameList :: [HsName] -> [String]
deHsNameList = map deHsName

-------------------------  Declarations ------------------------------
instance HsToCt HsDecl CtDecl where
	convert (HsTypeDecl loc name nameList htype) = CtTypeDecl (srcLine loc) (deHsName name) (map deHsName nameList) (convert htype)
	convert (HsDataDecl loc context name nameList constrList derives) = CtDataDecl (srcLine loc) (deHsName name) (map deHsName nameList) (map convert constrList)
	convert (HsNewTypeDecl pos context name nameList constr derives) = CtNewTypeDecl (srcLine pos) (deHsName name) (map deHsName nameList) (convert constr)

	--m{spacing=False}
	-- special case for empty class declaration
	convert (HsClassDecl pos context name nameList []) = CtClassDecl
	convert (HsClassDecl pos context name nameList declList) = CtClassDecl

	-- m{spacing=False}
	-- special case for empty instance declaration
	convert (HsInstDecl pos context name args []) = CtInstDecl
	convert (HsInstDecl pos context name args declList) = CtInstDecl
	convert (HsDefaultDecl pos htypes) = error "HsDefaultDecl"
	convert (HsTypeSig pos nameList qualType) = CtTypeSig (srcLine pos) (map deHsName nameList) (convert qualType)
	convert (HsFunBind matches) = CtFunBind (map convert matches)
	convert (HsPatBind pos pat rhs whereDecls) = CtPatBind (srcLine pos) (convert pat) (convert . deHsRhs $ rhs) (map convert whereDecls)
	convert (HsInfixDecl pos assoc prec opList) = CtInfixDecl	

{-
instance HsToCt HsAssoc where
	convert HsAssocNone  = undefined
	convert HsAssocLeft  = undefined
	convert HsAssocRight = undefined
-}
instance HsToCt HsMatch CtMatch where
	convert (HsMatch pos f ps rhs whereDecls) = CtMatch (srcLine pos) (deHsName f) (map convert ps) (convert . deHsRhs $ rhs) (map convert whereDecls)


------------------------- Data & Newtype Bodies -------------------------
deHsBangedType :: HsBangType -> HsType
deHsBangedType (HsBangedTy _)       = error "HsBangedTy"
deHsBangedType (HsUnBangedTy htype) = htype

instance HsToCt HsConDecl CtConDecl where
	convert (HsRecDecl _pos name fieldList) = error "HsRecDecl"
	--convert (HsConDecl _pos name@(HsSymbol _) [l, r]) = undefined
	convert (HsConDecl _pos name typeList) = CtConDecl (srcLine _pos) (deHsName name) (map (convert . deHsBangedType) typeList)

{-
instance HsToCt HsBangType where
	convert (HsBangedTy ty) = undefined
	convert (HsUnBangedTy ty) = undefined
-}

------------------------- Types -------------------------
instance HsToCt HsQualType CtType where
	convert (HsQualType context htype) = convert htype



deHsQName :: HsQName -> String
deHsQName (Qual m name)  = (deModule m) ++ "." ++ (deHsName name)
deHsQName (Special t) = pp t -- error "What's a 'special' type?"
  where pp HsUnitCon      = "()"     	-- ^ unit type and data constructor @()@
	pp HsListCon      = "[]"	-- ^ list type constructor @[]@
	pp HsFunCon       = "(->)"	-- ^ function type constructor @->@
	pp (HsTupleCon i) = "("++show i++"-tuple)" -- ^ /n/-ary tuple type 
	pp HsCons	  = ":"                    -- ^ list constructor @(:)@
deHsQName (UnQual name)  = deHsName name


instance HsToCt HsType CtType where
	convert (HsTyFun a b) = CtTyFun (convert a) (convert b)
	convert (HsTyTuple l) = CtTyTuple (map convert l)
	convert (HsTyApp a b) = CtTyApp (convert a) (convert b)
	convert (HsTyVar name) = CtTyVar (deHsName name)
	convert (HsTyCon name) = CtTyCon (deHsQName name)

deHsRhs :: HsRhs -> HsExp
deHsRhs (HsUnGuardedRhs e) = e
deHsRhs (HsGuardedRhss  _) = error "HsGuardedRhss"

{-
------------------------- Expressions -------------------------
instance HsToCt HsRhs where
	convert (HsUnGuardedRhs e) = undefined
	convert (HsGuardedRhss guardList) = undefined

instance HsToCt HsGuardedRhs where
	convert (HsGuardedRhs _pos guard body) = undefined
-}
instance HsToCt HsLiteral CtLiteral where
	convert (HsInt i)        = CtInt i
	convert (HsChar c)       = CtChar c
	convert (HsString s)     = CtString s
	convert (HsFrac r)       = CtFrac r
	-- GHC unboxed literals:
	convert (HsCharPrim c)   = error "HsCharPrim"
	convert (HsStringPrim s) = error "HsStringPrim"
	convert (HsIntPrim i)    = error "HsIntPrim"
	convert (HsFloatPrim r)  = error "HsFloatPrim"
	convert (HsDoublePrim r) = error "HsDoublePrim"

deHsQOp :: HsQOp -> String
deHsQOp (HsQVarOp n) = deHsQName n
deHsQOp (HsQConOp n) = deHsQName n

instance HsToCt HsExp CtExp where
	convert (HsLit l) =  CtLit (convert l)
	-- lambda stuff
	convert (HsInfixApp a op b) = CtInfixApp (convert a) (deHsQOp op) (convert b)
	convert (HsNegApp e) = CtNegApp (convert e)
	convert (HsApp a b) = CtApp (convert a) (convert b)
	convert (HsLambda _loc patList body) = CtLambda (srcLine _loc) (map convert patList) (convert body)
	-- keywords
	convert (HsLet declList letBody) = CtLet (map convert declList) (convert letBody)
	convert (HsIf cond thenexp elsexp) = CtIf (convert cond) (convert thenexp) (convert elsexp)
	convert (HsCase cond altList) = CtCase (convert cond) (map convert altList)
	convert (HsDo stmtList) = error "HsDo"
	-- Constructors & Vars
	convert (HsVar name) = CtVar (deHsQName name)
	convert (HsCon name) = CtCon(deHsQName name)
	convert (HsTuple expList) = CtTuple (map convert expList)
	-- weird stuff
	convert (HsParen e) = CtParen (convert e)
	convert (HsLeftSection e op) = error "HsLeftSection"
	convert (HsRightSection op e) = error "HsRightSection"
	convert (HsRecConstr c fieldList) = error "HsRecConstr"
	convert (HsRecUpdate e fieldList) = error "HsRecUpdate"
	-- patterns
	-- special case that would otherwise be buggy
	convert (HsAsPat name (HsIrrPat e)) = error "HsAsPat-HsIrrPat"
	convert (HsAsPat name e) = error "HsAsPat"
	convert HsWildCard = error "HsWildCard"
	convert (HsIrrPat e) = error "HsIrrPat"
	-- Lists
	convert (HsList list) = CtList (map convert list)
	convert (HsEnumFrom e) = error "HsEnumFrom"
	convert (HsEnumFromTo from to) = error "HsEnumFromTo"
	convert (HsEnumFromThen from thenE) = error "HsEnumFromThen"
	convert (HsEnumFromThenTo from thenE to) = error "HsEnumFromThenTo"
	convert (HsListComp e stmtList) = error "HsListComp"
	convert (HsExpTypeSig _pos e ty) = error "HsExpTypeSig"

------------------------- Patterns -----------------------------
instance HsToCt HsPat CtPat where
	convert (HsPVar name) = CtPVar (deHsName name)
	convert (HsPLit lit) = CtPLit (convert lit)
	convert (HsPNeg p) = error "HsPNeg"
	convert (HsPInfixApp a op b) = CtPInfixApp (convert a) (deHsQName op) (convert b)
	convert (HsPApp n ps) = CtPApp (deHsQName n) (map convert ps)
	convert (HsPTuple ps) = CtPTuple (map convert ps)
	convert (HsPList ps) = CtPList (map convert ps)
	convert (HsPParen p) = CtPParen (convert p)
	convert (HsPRec c fields) = error "HsPRec"
	-- special case that would otherwise be buggy
	convert (HsPAsPat name (HsPIrrPat pat)) = error "HsPAsPat-HsPIrrPat"
	convert (HsPAsPat name pat) = error "HsAsPat"
	convert HsPWildCard = CtPWildCard
	convert (HsPIrrPat pat) = error "HsPIrrPat"

{-
instance HsToCt HsPatField where
	convert (HsPFieldPat name pat) = undefined
-}

deHsGuardedAlts :: HsGuardedAlts -> HsExp
deHsGuardedAlts (HsUnGuardedAlt e) = e
deHsGuardedAlts (HsGuardedAlts _)  = error "HsGuardedAlts"

------------------------- Case bodies  -------------------------
instance HsToCt HsAlt CtAlt where
	convert (HsAlt _pos pat gAlts decls) = CtAlt (srcLine _pos) (convert pat) (convert . deHsGuardedAlts $ gAlts) (map convert decls)

{-
instance HsToCt HsGuardedAlts where
	convert (HsUnGuardedAlt e) = undefined
	convert (HsGuardedAlts altList) = undefined

instance HsToCt HsGuardedAlt where
	convert (HsGuardedAlt _pos e body) = undefined


------------------------- Statements in monads & list comprehensions -----
instance HsToCt HsStmt where
	convert (HsGenerator _loc e from) = undefined
	convert (HsQualifier e) = undefined
	convert (HsLetStmt declList) = undefined

------------------------- Record updates
instance HsToCt HsFieldUpdate where
	convert (HsFieldUpdate name e) = undefined

------------------------- Names -------------------------
instance HsToCt HsQOp where
	convert (HsQVarOp n) = undefined
	convert (HsQConOp n) = undefined

instance HsToCt HsQName where
	convert name = undefined

instance HsToCt HsOp where
	convert (HsVarOp n) = undefined
	convert (HsConOp n) = undefined

instance HsToCt HsName where
	convert name = undefined

instance HsToCt HsCName where
	convert (HsVarName n) = undefined
	convert (HsConName n) = undefined

-}
