module Assorted where

import MonadicConstructions
import CommonTypes
import MonadicBoilerplate
import Syntax
import Parser
import IO
import System.IO.Unsafe 


gettypesigs :: [CtDecl] -> [CtDecl]
gettypesigs = filter ts
  where ts (CtTypeSig _ _ _) = True
        ts _                 = False

getpatbinds :: [CtDecl] -> [CtDecl]
getpatbinds = filter pbs
  where pbs (CtPatBind _ _ _ _) = True
        pbs _                   = False

ac = "AddingContext.hs"

typesigs = gettypesigs . projDecls . parseCt
patbinds = getpatbinds . projDecls . parseCt

gots = showDecls . typesigs
gods = showDecls . patbinds

mkfunbind :: CtDecl -> (Name, CtExp)
mkfunbind (CtPatBind l (CtPVar f) body []) = (f,body)
mkfunbind (CtPatBind l _ _ _)              = error $ "Problem at line " ++ show l

mktypebind :: CtDecl -> (Name, CtType)
mktypebind (CtTypeSig l [f] t) = (f,t)
mktypebind (CtTypeSig l _ _)   = error $ "Problem at line " ++ show l

{- The mlab parser returns a list of Layer's:
data Layer
  = Io  
  | List  
  | ErrorT ErrorName TypeQ  
  | StateT StateName TypeQ
  | EnvT EnvName TypeQ
  | WriterT WriterName TypeQ
  | ContT TypeQ
  | ResT MonadName

You can get the states from these layers.
-}

--CtTypeSig :: Line -> [Name] -> CtType -> CtDecl
--CtPatBind :: Line -> CtPat -> CtExp -> [CtDecl] -> CtDecl

----------------------------------------
--        Using the front end         --
----------------------------------------

{-
compile :: String -> IO ()
compile file = doit $ projDecls $ parseCt file
-}

parseCt :: String -> CtModule
parseCt = unsafePerformIO . parseFile
     where parseFile :: String -> IO CtModule
           parseFile file = do
	                       h <- openFile file ReadMode
	                       contents <- hGetContents h
	                       return . parser $ contents

projDecls (CtModule _ _ ds) = ds

showDecls :: [CtDecl] -> IO ()
showDecls []     = putStrLn ""
showDecls (d:ds) = putStrLn (show d) >>
                   putStrLn "" >>
                   showDecls ds

