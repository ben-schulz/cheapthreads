module CT.Recursion where

import CT.Syntax
import Data.List
import Data.Maybe
import Data.Graph
import Data.Ord
import Control.Monad.State
import Control.Monad.Identity

--
-- Group each maximal set of (possibly mutually) recursively defined FunDecls
-- into a single RecDecl. Decls are returned in order of source file position,
-- except that RecDecls appear where their earliest-defined FunDecl would have
-- appeared, and FunDecls of recursive functions are moved inside the
-- corresponding FunDecl. FunDecls inside of a RecDecl are sorted by source
-- file position. All decls retain their originally source position tag, even
-- if they have been "moved".
--
-- For example, if f is defined on line 1, g is defined on line 2, h is defined
-- on line 3, and f and h are mutually recursive but g is non-recursive, the
-- first decl will be a RecDecl containing FunDecls for f (tagged with line 1)
-- and h (tagged with line 3) in that order, and the second decl will be a
-- FunDecl for g (tagged with line 2).
--
groupDecls :: CtsProg -> CtsProg
groupDecls prog = CtsProg $ sortDecls (concatMap declsFromSCC progSCCs ++ rest)
                  where
                     (CtsProg decls) = prog
                     g               = buildCallGraph prog
                     progSCCs        = sccs g
                     
                     declPos (CtsMonadDecl p _ _)  = p
                     declPos (CtsFunTySig p _ _ _) = p
                     declPos (CtsFunDecl p _ _ _)  = p
                     declPos (CtsRecDecl ds)       = declPos (head ds)
                     declPos (CtsTypeDecl p _ _)   = p
                     declPos (CtsDataDecl p _ _)   = p
                     
                     sortDecls = sortBy (comparing declPos)
                     
                     declName :: CtsDecl -> Maybe CtsIdent
                     declName (CtsFunDecl _ n _ _)  = Just n
                     declName _                     = Nothing
                     
                     declsFromSCC :: SCC CtsIdent -> [CtsDecl]
                     declsFromSCC (AcyclicSCC n) = sortDecls $ filter (\d -> declName d == Just n) decls
                     declsFromSCC (CyclicSCC ns) = [CtsRecDecl $ filter (\d -> declName d `elem` (map Just ns)) decls]

                     rest = filter (isNothing . declName) decls
--
-- Find SCCs in the call graph
--
sccs :: CallGraph -> [SCC CtsIdent]
sccs g = stronglyConnComp g'
         where
            -- Massage the data into a form that Data.Graph likes
            -- ("node" distinct from "key")
            g' = map (\(n,ns) -> (n,n,ns)) g
         

--
-- Build the call graph (FIXME: sort of inefficient)
--
type CallGraph = [(CtsIdent,[CtsIdent])]
type EdgeList = [(CtsIdent,CtsIdent)]

progNodes :: CtsProg -> [CtsIdent]
progNodes (CtsProg decls) = concatMap declNodes decls
                            where
                               declNodes :: CtsDecl -> [CtsIdent]
                               declNodes (CtsFunDecl _ name _ _) = [name]
                               declNodes (CtsRecDecl ds)         = concatMap declNodes ds
                               declNodes _                       = []

buildCallGraph :: CtsProg -> CallGraph
buildCallGraph prog = let
                         edgelist         = buildEdgeList prog
                         nodes            = progNodes prog
                         callerCallees cr = nub [callee|(caller,callee) <- edgelist, caller == cr]
                         g                = map (\cr -> (cr,callerCallees cr)) nodes
                      in
                         g

buildEdgeList :: CtsProg -> EdgeList
buildEdgeList (CtsProg decls) = declsEdgeList decls

declsEdgeList :: [CtsDecl] -> EdgeList
declsEdgeList ((CtsFunDecl _ name params body):ds) = zip (repeat name) (callees body params) ++ declsEdgeList ds
declsEdgeList (_:ds)                               = declsEdgeList ds
declsEdgeList []                                   = []

callees :: CtsExpr -> [CtsIdent] -> [CtsIdent]
callees (CtsApp ident args _) shadowed          = let
                                                     myCallees  = if ident `elem` shadowed then [] else [ident]
                                                     argCallees = concatMap (\e -> callees e shadowed) args
                                                  in
                                                     myCallees ++ argCallees
callees (CtsFixApp idents body args _) shadowed = let
                                                     bodyCallees = callees body (idents ++ shadowed)
                                                     argCallees  = concatMap (\e -> callees e shadowed) args
                                                  in
                                                     bodyCallees ++ argCallees

--
-- case for semifix; (2009.11.09 Schulz)
--
callees (CtsSemiFixApp sent idents body args _) shadowed = let
                                                             bodyCallees = callees body (idents ++ shadowed)
                                                             argCallees  = concatMap (\e -> callees e shadowed) args
                                                           in
                                                             bodyCallees ++ argCallees
--
-- end change
--

callees (CtsInfixApp e1 _ e2 _) shadowed        = callees e1 shadowed ++ callees e2 shadowed
callees (CtsConstrApp _ args _) shadowed        = concatMap (\e -> callees e shadowed) args
callees (CtsLitExpr _ _) _                      = []
callees (CtsVar ident _) shadowed               = if ident `elem` shadowed then [] else [ident]
callees (CtsNeg e _) shadowed                   = callees e shadowed
callees (CtsIfThenElse e t f _) shadowed        = callees e shadowed ++ callees t shadowed ++ callees f shadowed
callees (CtsCase e alts _) shadowed             = callees e shadowed ++ concatMap (\a -> altCallees a) alts
                                                   where
                                                      altCallees (CtsAlt (CtsPConstr _ idents) body) = callees body (idents ++ shadowed)
                                                      altCallees (CtsAlt (CtsPTuple idents) body)    = callees body (idents ++ shadowed)
                                                      -- 
                                                      -- the wildcard is a kludge to ram through SecureQ; 
                                                      -- something else is probably called-for handle the other patterns:
                                                      -- 
                                                      -- 07.07.09 Schulz
                                                      altCallees _                                   = [ ]
callees (CtsTuple args _) shadowed              = concatMap (\e -> callees e shadowed) args
callees (CtsList args _) shadowed               = concatMap (\e -> callees e shadowed) args
callees (CtsUnit _) _                           = []
callees (CtsEmptyList _) _                      = []
callees (CtsBind e1 ident e2 _) shadowed        = callees e1 shadowed ++ callees e2 (ident : shadowed)
callees (CtsBindNull e1 e2 _) shadowed          = callees e1 shadowed ++ callees e2 shadowed
callees (CtsReturn e _) shadowed                = callees e shadowed
