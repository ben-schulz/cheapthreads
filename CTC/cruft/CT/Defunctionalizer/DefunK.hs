--
-- this is ~/cheapthreads/ctc/ct/defunctionalizer/DefunK.hs
--
-- defunctionalizer for the K monad
--
-- put here 27.01.09 Schulz
--


module CT.Defunctionalizer.DefunK where

import Control.Monad

import CT.Syntax
import CT.Defunctionalizer.DefunTypes
import CT.Defunctionalizer.PreDefun
import CT.Defunctionalizer.BMonad

--                         --
-- MAIN K-DEFUNCTIONALIZER --
--                         --

defunKPlus :: CtsExpr -> KRulePlus
defunKPlus expr@(CtsApp _ _ _)
  | isPut expr = let i = specPut expr
                     e = exprPut expr
                 in
                   \ s -> writeKPlus vIdent (return DFUnit) $
                            writeKPlus i (evalCtsExprPlus s e) s
  | isGet expr = let i = specGet expr
                 in
                   readxPlus i
  | otherwise  = error $ "in defunK: attempt to defunctionalize " ++ show expr
                         ++ " which is an application of neither"
                         ++ " 'put' nor 'get'"

defunKPlus (CtsReturn e _) = \ s -> writeKPlus vIdent (evalCtsExprPlus s e) s

defunKPlus (CtsBind e1 x e2 _) =
  let p = defunKPlus e1
      g = defunKPlus e2
  in
    g . (updPlus x) . p

defunKPlus (CtsBindNull e1 e2 _) =
  let p = defunKPlus e1
      g = defunKPlus e2
  in
    g . p

-- read and write are treated as primitives but translated into
-- the equivalent of 'get' and 'put' to the appropriate memory locations
defunKPlus (CtsTuple (op:args) t)

  | "read" == (nameOf op) =
    let mem  =  nameOf $ head args
        addr =  head $ tail args
    in
      \s -> let loc = runB $ evalCtsExprPlus s addr
            in
              writeKPlus vIdent (V $ DFMemRead mem loc) s

  -- we are artificially constraining the expression form in
  -- 'exp'; see log 2009.11.16
  | "write" == (nameOf op) =
    let mem  = nameOf $ head args
        addr = head $ tail args
        exp  = head $ tail $ tail args
        translate = \q -> case q of
                            DFPOp (FSMPlus u v)  -> MValExpr Minus 
                                                     (translate u) (translate v)
                            DFPOp (FSMMinus u v) -> MValExpr Minus 
                                                     (translate u) (translate v)
                            DFPOp (FSMMult u v)  -> MValExpr Mult
                                                     (translate u) (translate v)
                            (DFInt n)      -> LitMVal n
                            (DFParam s)    -> SymMVal s
    in
      \s -> let val = case (runB $ evalCtsExprPlus s exp) of
                        (DFInt n)    -> LitMVal n
                        (DFParam s)  -> SymMVal s
                        p@(DFPOp _)  -> translate p
                        x            -> error $ "in defunK: memory write: " ++
                                               (show x)
                loc = case (runB $ evalCtsExprPlus s addr) of
                        (DFInt n)   -> LitMVal n
                        (DFParam s) -> SymMVal s
                        p@(DFPOp _)  -> translate p
                        x           -> error $ "in defunK: memory write: " ++
                                               (show x)
            in
              writeKPlus mem (V $ DFMemWrite mem loc val) s

  | otherwise = error $ "in defunK: " ++ (nameOf op) ++
                         " should not be a top-level K-primitive"
defunKPlus e = error $ "\n\nin defunK: no appropriate pattern for "
                     ++ "K-defunctionalization of " ++ show e

--
-- old version with old types:
--

{-

--
-- shut off while working, to avoid extraneous type conflicts
--
-- 20.07.09 Schulz
--
defunK :: CtsExpr -> KRule
defunK expr@(CtsApp _ _ _)
  | isPut expr = let i = specPut expr
                     e = exprPut expr
                 in
                   \ s -> writeK vIdent DFUnit $ writeK i (evalCtsExpr s e) s
  | isGet expr = let i = specGet expr
                 in
                   readx i
  | otherwise  = error $ "in defunK: attempt to defunctionalize " ++ show expr
                         ++ " which is an application of neither"
                         ++ " 'put' nor 'get'"
defunK (CtsReturn e _) = \ s -> writeK vIdent (evalCtsExpr s e) s
defunK (CtsBind e1 x e2 _) =
  let p = defunK e1
      g = defunK e2
  in
    g . (upd x) . p
defunK (CtsBindNull e1 e2 _) =
  let p = defunK e1
      g = defunK e2
  in
    g . p
defunK e = error $ "in defunK: no appropriate pattern for "
                   ++ "K-defunctionalization of " ++ show e
-}


--
-- upd
--
-- as defined in the paper
--
upd :: CtsIdent -> KState -> KState
upd x = \s -> case lookup vIdent s of
                Nothing -> varNotFound $ "in upd: " ++ vIdent
                Just k   -> writeK x k s

--
-- same as above with different type signature
--
updPlus :: CtsIdent -> KStatePlus -> KStatePlus
updPlus x = \s -> case lookup vIdent s of
                    Nothing -> varNotFound $ "in upd: " ++ vIdent
                    Just k   -> writeKPlus x k s

--
-- readx
--
-- as defined in the paper
--

readx :: CtsIdent -> KState -> KState
readx x = \s -> case lookup x s of
                  Nothing ->  varNotFound $ "in readx: " ++ x
                  Just k   -> writeK vIdent k s

--
-- same as above, just with different type signature
--
readxPlus :: CtsIdent -> KStatePlus -> KStatePlus
readxPlus x = \s -> case lookup x s of
                      Nothing ->  varNotFound $ "in readx: " ++ x
                      Just k   -> writeKPlus vIdent k s

--
-- write a new value to a specific key in the state
--
writeK :: CtsIdent -> DefunVal -> KState -> KState
writeK k v xs = let w (x, y) = if (x == k) then (x, v) else (x, y)
              in
              map w xs

--
-- modified to accomodate conditional values
--
-- 15.07.09 Schulz
--
writeKPlus :: CtsIdent -> RHVal -> KStatePlus -> KStatePlus
writeKPlus k v xs = let w (x, y) = if (x == k) then (x, v) else (x, y)
                    in
                      map w xs

--
-- a simple CtsExpr evaluator
--

{-

--
-- This is an old version; the data types have been changed,
-- as reflected in evalCtsExprPlus.
--
-- shut off while working to avoid extraneous type conflicts
--
-- 20.07.09 Schulz
--
evalCtsExpr :: KState -> CtsExpr -> DefunVal
evalCtsExpr _ (CtsLitExpr lit _) = ctsLitToVal lit
evalCtsExpr s (CtsVar x _) =
  case lookup x s of
    Nothing -> varNotFound $ "for identifier in evalCtsExpr: " ++ x
--    Nothing -> error $ show x ++ "\n\n" ++ show s
    Just v  -> v
evalCtsExpr s (CtsApp f args _)
  | "+" == f  = let [x, y] = args
                    u = evalCtsExpr s x
                    v = evalCtsExpr s y
                in
                  (liftM DFPOp) (liftM2 DFPlus) u v
  | "-" == f  = let [x, y] = args
                    u = evalCtsExpr s x
                    v = evalCtsExpr s y
                in
                  (liftM DFPOp) (liftM2 DFMinus) u v
  | "==" == f  = let [x, y] = args
                     u = evalCtsExpr s x
                     v = evalCtsExpr s y
                 in
                   (liftM DFPOp) (liftM2 DFEquality) u v
{-
 -- please ignore this; the code here has been deprecated
 -- 2009.11.18 Schulz
  | "!=" == f  = let [x, y] = args
                     u = evalCtsExpr s x
                     v = evalCtsExpr s y
                 in
                   (liftM DFPOp) (liftM2 DFInequality) u v
  | "&&" == f  = let [x, y] = args
                     u = evalCtsExpr s x
                     v = evalCtsExpr s y
                 in
                   (liftM DFPOp) (liftM2 DFInquality) u v
  | "||" == f  = let [x, y] = args
                     u = evalCtsExpr s x
                     v = evalCtsExpr s y
                 in
                   (liftM DFPOp) (liftM2 DFInquality) u v
-}
  | otherwise = error $ "in evalCtsExpr: no definition for function " ++ f
evalCtsExpr s (CtsInfixApp e1 f e2 t) =
  evalCtsExpr s (CtsApp f [e1, e2] t)
evalCtsExpr s (CtsNeg expr _) =
  dfvNeg (evalCtsExpr s expr)
evalCtsExpr s (CtsIfThenElse p e1 e2 _) =
--  error "evaluating if-then-else expressions as ordinary values is deprecated"
  case evalCtsExpr s p of
    DFPOp (DFEquality u v)   -> DFPOp (DFEquality u v) -- kludge 09.07.09
    DFPOp (DFInequality u v) -> DFPOp (DFInequality u v) -- kludge 09.07.09
    DFBool True  -> evalCtsExpr s e1
    DFBool False -> evalCtsExpr s e2
    _            -> badType (show p)
evalCtsExpr s (CtsCase e1 ofs _) =
  case dropWhile (not . (ctsAltMatch e1)) ofs of
    [ ]                 -> patMatchFail (show e1) (show ofs)
    ((CtsAlt pat e2):_) -> evalCtsExpr ((pBindLocal e1 s pat) ++ s) e2
evalCtsExpr s (CtsTuple (c:cs) _) =  -- THIS IS A KLUDGE (see log 04.03.09)
  let e1 = evalCtsExpr s $ head cs
      e2 = evalCtsExpr s $ (head . tail) cs
  in
    if "+" == nameOf c
    then
      DFPOp $ DFPlus e1 e2
    else if "-" == nameOf c
    then
      DFPOp $ DFMinus e1 e2
    else error $ "no general case for tuples in evalCtsExpr"

evalCtsExpr s (CtsSignalReq sig _) =
  case sig of
    Cont     -> DFContReq
    GetPorts -> DFPortsReq

evalCtsExpr s (CtsConstrApp c args _) =
  DFConstrVal c $ map (evalCtsExpr s) args

evalCtsExpr s x = error $ "in evalCtsExpr: no case for " ++ (show x)

-}

--
-- redone evaluator; this one uses the 'conditional' values
--
-- 13.07.09 Schulz
--

evalCtsExprPlus :: KStatePlus -> CtsExpr -> RHVal
evalCtsExprPlus _ (CtsLitExpr lit _) = return $ ctsLitToVal lit
evalCtsExprPlus s (CtsVar x _) =
  case lookup x s of
--    Nothing -> varNotFound $ "for identifier in evalCtsExpr: " ++ x
    Nothing -> varNotFound $ "\n\n" ++ x ++ "\n\n" ++ (show s)
    Just v  -> v
evalCtsExprPlus s (CtsApp f args _)

  | "+" == f  =
    let [x, y] = args
    in
      case evalCtsExprPlus s x of
        b@(C p e1 e2) -> case evalCtsExprPlus s y of

                           b'@(C p' e1' e2') -> let b''  = refine p b'
                                                    e1'' = do
                                                             v <- b''
                                                             u <- e1
                                                             return $ DFPOp $
                                                               FSMPlus u v
                                                    e2'' = do
                                                             v <- b''
                                                             u <- e2
                                                             return $ DFPOp $
                                                               FSMPlus u v
                                                 in
                                                   (C p e1'' e2'')

                           (V t')            -> b >>=
                                                 (return . DFPOp . (FSMPlus t'))

        b@(V t)     -> case evalCtsExprPlus s y of

                         (C _ _ _) -> b >>= \x ->
                                              return $ DFPOp $ FSMPlus x t

                         (V t')    -> return $ DFPOp $ FSMPlus t t'

  | "-" == f  =
    let [x, y] = args
    in
      case evalCtsExprPlus s x of
        b@(C p e1 e2) -> case evalCtsExprPlus s y of

                           b'@(C p' e1' e2') -> let b''  = refine p b'
                                                    e1'' = do
                                                             v <- b''
                                                             u <- e1
                                                             return $ DFPOp $
                                                               FSMMinus u v
                                                    e2'' = do
                                                             v <- b''
                                                             u <- e2
                                                             return $ DFPOp $
                                                               FSMMinus u v
                                                 in
                                                   (C p e1'' e2'')

                           (V t')            -> b >>=
                                                (return . DFPOp . (FSMMinus t'))

        b@(V t)     -> case evalCtsExprPlus s y of

                         (C _ _ _) -> b >>= \x ->
                                              return $ DFPOp $ FSMMinus x t

                         (V t')    -> return $ DFPOp $ FSMMinus t t'
  | "*" == f  =
    let [x, y] = args
    in
      case evalCtsExprPlus s x of
        b@(C p e1 e2) -> case evalCtsExprPlus s y of

                           b'@(C p' e1' e2') -> let b''  = refine p b'
                                                    e1'' = do
                                                             v <- b''
                                                             u <- e1
                                                             return $ DFPOp $
                                                               FSMMult u v
                                                    e2'' = do
                                                             v <- b''
                                                             u <- e2
                                                             return $ DFPOp $
                                                               FSMMult u v
                                                 in
                                                   (C p e1'' e2'')

                           (V t')            -> b >>=
                                                 (return . DFPOp . (FSMMult t'))

        b@(V t)     -> case evalCtsExprPlus s y of

                         (C _ _ _) -> b >>= \x ->
                                              return $ DFPOp $ FSMMult x t

                         (V t')    -> return $ DFPOp $ FSMMult t t'

  | "&&&" == f  =
    let [x, y] = args
    in
      case evalCtsExprPlus s x of
        b@(C p e1 e2) -> case evalCtsExprPlus s y of

                           b'@(C p' e1' e2') -> let b''  = refine p b'
                                                    e1'' = do
                                                             v <- b''
                                                             u <- e1
                                                             return $ DFPOp $
                                                               FSMBWAnd u v
                                                    e2'' = do
                                                             v <- b''
                                                             u <- e2
                                                             return $ DFPOp $
                                                               FSMBWAnd u v
                                                 in
                                                   (C p e1'' e2'')

                           (V t')            -> b >>=
                                                 (return . DFPOp . (FSMBWAnd t'))

        b@(V t)     -> case evalCtsExprPlus s y of

                         (C _ _ _) -> b >>= \x ->
                                              return $ DFPOp $ FSMBWAnd x t

                         (V t')    -> return $ DFPOp $ FSMBWAnd t t'

  | "|||" == f  =
    let [x, y] = args
    in
      case evalCtsExprPlus s x of
        b@(C p e1 e2) -> case evalCtsExprPlus s y of

                           b'@(C p' e1' e2') -> let b''  = refine p b'
                                                    e1'' = do
                                                             v <- b''
                                                             u <- e1
                                                             return $ DFPOp $
                                                               FSMBWOr u v
                                                    e2'' = do
                                                             v <- b''
                                                             u <- e2
                                                             return $ DFPOp $
                                                               FSMBWOr u v
                                                 in
                                                   (C p e1'' e2'')

                           (V t')            -> b >>=
                                                 (return . DFPOp . (FSMBWOr t'))

        b@(V t)     -> case evalCtsExprPlus s y of

                         (C _ _ _) -> b >>= \x ->
                                              return $ DFPOp $ FSMBWOr x t

                         (V t')    -> return $ DFPOp $ FSMBWOr t t'


  | "==" == f  =
    let [x, y] = args
    in
      case evalCtsExprPlus s x of
        b@(C p e1 e2) -> case evalCtsExprPlus s y of

                           b'@(C p' e1' e2') -> let b''  = refine p b'
                                                    e1'' = do
                                                             v <- b''
                                                             u <- e1
                                                             return $ DFPOp $
                                                               FSMEquality u v
                                                    e2'' = do
                                                             v <- b''
                                                             u <- e2
                                                             return $ DFPOp $
                                                               FSMEquality u v
                                                 in
                                                   (C p e1'' e2'')

                           (V t')            -> b >>=
                                                (return.DFPOp.(FSMEquality t'))

        b@(V t)     -> case evalCtsExprPlus s y of

                         (C _ _ _) -> b >>= \x ->
                                              return $ DFPOp $ FSMEquality x t

                         (V t')    -> return $ DFPOp $ FSMEquality t t'
  | "!=" == f  =
    let [x, y] = args
    in
      case evalCtsExprPlus s x of
        b@(C p e1 e2) -> case evalCtsExprPlus s y of

                           b'@(C p' e1' e2') -> let b''  = refine p b'
                                                    e1'' = do
                                                             v <- b''
                                                             u <- e1
                                                             return $ DFPOp $
                                                               FSMInequality u v
                                                    e2'' = do
                                                             v <- b''
                                                             u <- e2
                                                             return $ DFPOp $
                                                               FSMInequality u v
                                                 in
                                                   (C p e1'' e2'')

                           (V t')           -> b >>=
                                               (return.DFPOp.(FSMInequality t'))

        b@(V t)     -> case evalCtsExprPlus s y of

                         (C _ _ _) -> b >>= \x ->
                                              return $ DFPOp $ FSMInequality x t

                         (V t')    -> return $ DFPOp $ FSMInequality t t'


  | "&&" == f  =
    let [x, y] = args
    in
      case evalCtsExprPlus s x of
        b@(C p e1 e2) -> case evalCtsExprPlus s y of

                           b'@(C p' e1' e2') -> let b''  = refine p b'
                                                    e1'' = do
                                                             v <- b''
                                                             u <- e1
                                                             return $ DFPOp $
                                                               FSMAnd u v
                                                    e2'' = do
                                                             v <- b''
                                                             u <- e2
                                                             return $ DFPOp $
                                                               FSMAnd u v
                                                 in
                                                   (C p e1'' e2'')

                           (V t')           -> b >>=
                                               (return.DFPOp.(FSMAnd t'))

        b@(V t)     -> case evalCtsExprPlus s y of

                         (C _ _ _) -> b >>= \x ->
                                              return $ DFPOp $ FSMAnd x t

                         (V t')    -> return $ DFPOp $ FSMAnd t t'

  | "||" == f  =
    let [x, y] = args
    in
      case evalCtsExprPlus s x of
        b@(C p e1 e2) -> case evalCtsExprPlus s y of

                           b'@(C p' e1' e2') -> let b''  = refine p b'
                                                    e1'' = do
                                                             v <- b''
                                                             u <- e1
                                                             return $ DFPOp $
                                                               FSMOr u v
                                                    e2'' = do
                                                             v <- b''
                                                             u <- e2
                                                             return $ DFPOp $
                                                               FSMOr u v
                                                 in
                                                   (C p e1'' e2'')

                           (V t')           -> b >>=
                                               (return.DFPOp.(FSMOr t'))

        b@(V t)     -> case evalCtsExprPlus s y of

                         (C _ _ _) -> b >>= \x ->
                                              return $ DFPOp $ FSMOr x t

                         (V t')    -> return $ DFPOp $ FSMOr t t'


  | "<" == f  =
    let [x, y] = args
    in
      case evalCtsExprPlus s x of
        b@(C p e1 e2) -> case evalCtsExprPlus s y of

                           b'@(C p' e1' e2') -> let b''  = refine p b'
                                                    e1'' = do
                                                             v <- b''
                                                             u <- e1
                                                             return $ DFPOp $
                                                               FSMLTTest u v
                                                    e2'' = do
                                                             v <- b''
                                                             u <- e2
                                                             return $ DFPOp $
                                                               FSMLTTest u v
                                                 in
                                                   (C p e1'' e2'')

                           (V t')           -> b >>=
                                               (return.DFPOp.(FSMLTTest t'))

        b@(V t)     -> case evalCtsExprPlus s y of

                         (C _ _ _) -> b >>= \x ->
                                              return $ DFPOp $ FSMLTTest x t

                         (V t')    -> return $ DFPOp $ FSMLTTest t t'
  | ">" == f  =
    let [x, y] = args
    in
      case evalCtsExprPlus s x of
        b@(C p e1 e2) -> case evalCtsExprPlus s y of

                           b'@(C p' e1' e2') -> let b''  = refine p b'
                                                    e1'' = do
                                                             v <- b''
                                                             u <- e1
                                                             return $ DFPOp $
                                                               FSMGTTest u v
                                                    e2'' = do
                                                             v <- b''
                                                             u <- e2
                                                             return $ DFPOp $
                                                               FSMGTTest u v
                                                 in
                                                   (C p e1'' e2'')

                           (V t')           -> b >>=
                                               (return.DFPOp.(FSMGTTest t'))

        b@(V t)     -> case evalCtsExprPlus s y of

                         (C _ _ _) -> b >>= \x ->
                                              return $ DFPOp $ FSMGTTest x t

                         (V t')    -> return $ DFPOp $ FSMGTTest t t'

  | "<=" == f  =
    let [x, y] = args
    in
      case evalCtsExprPlus s x of
        b@(C p e1 e2) -> case evalCtsExprPlus s y of

                           b'@(C p' e1' e2') -> let b''  = refine p b'
                                                    e1'' = do
                                                             v <- b''
                                                             u <- e1
                                                             return $ DFPOp $
                                                               FSMLTETest u v
                                                    e2'' = do
                                                             v <- b''
                                                             u <- e2
                                                             return $ DFPOp $
                                                               FSMLTETest u v
                                                 in
                                                   (C p e1'' e2'')

                           (V t')           -> b >>=
                                               (return.DFPOp.(FSMLTETest t'))

        b@(V t)     -> case evalCtsExprPlus s y of

                         (C _ _ _) -> b >>= \x ->
                                              return $ DFPOp $ FSMLTETest x t

                         (V t')    -> return $ DFPOp $ FSMLTETest t t'


  | ">=" == f  =
    let [x, y] = args
    in
      case evalCtsExprPlus s x of
        b@(C p e1 e2) -> case evalCtsExprPlus s y of

                           b'@(C p' e1' e2') -> let b''  = refine p b'
                                                    e1'' = do
                                                             v <- b''
                                                             u <- e1
                                                             return $ DFPOp $
                                                               FSMGTETest u v
                                                    e2'' = do
                                                             v <- b''
                                                             u <- e2
                                                             return $ DFPOp $
                                                               FSMGTETest u v
                                                 in
                                                   (C p e1'' e2'')

                           (V t')           -> b >>=
                                               (return.DFPOp.(FSMGTETest t'))

        b@(V t)     -> case evalCtsExprPlus s y of

                         (C _ _ _) -> b >>= \x ->
                                              return $ DFPOp $ FSMGTETest x t

                         (V t')    -> return $ DFPOp $ FSMGTETest t t'



  | otherwise = error $ "in evalCtsExpr: no definition for function " ++ f


{-
  | "+" == f  = let [x, y] = args
                in
                  do
                    u <- evalCtsExprPlus s x
                    v <- evalCtsExprPlus s y
                    return $ FSMPlus u v
  | "-" == f  = let [x, y] = args
                in
                  do
                    u <- evalCtsExprPlus s x
                    v <- evalCtsExprPlus s y
                    return $ FSMMinus u v
  | "==" == f  = let [x, y] = args
                 in
                  do
                    u <- evalCtsExprPlus s x
                    v <- evalCtsExprPlus s y
                    return $ FSMEquality u v
  | otherwise = error $ "in evalCtsExpr: no definition for function " ++ f
-}

evalCtsExprPlus s (CtsInfixApp e1 f e2 t) =
  evalCtsExprPlus s (CtsApp f [e1, e2] t)
evalCtsExprPlus s (CtsNeg expr _) =
  do
    v <- evalCtsExprPlus s expr
    return $ dfvNeg v
evalCtsExprPlus s (CtsCase e1 ofs _) =
  case dropWhile (not . (ctsAltMatch e1)) ofs of
    [ ]                 -> patMatchFail (show e1) (show ofs)
    ((CtsAlt pat e2):_) -> evalCtsExprPlus ((pBindLocalPlus e1 s pat) ++ s) e2

evalCtsExprPlus s (CtsTuple (c:cs) t)
  | "+" == nameOf c =
    do
      e1 <- evalCtsExprPlus s $ head cs
      e2 <- evalCtsExprPlus s $ (head . tail) cs
      return $ DFPOp $ FSMPlus e1 e2
  | "-" == nameOf c =
    do
      e1 <- evalCtsExprPlus s $ head cs
      e2 <- evalCtsExprPlus s $ (head . tail) cs
      return $ DFPOp $ FSMMinus e1 e2
  | "*" == nameOf c =
    do
      e1 <- evalCtsExprPlus s $ head cs
      e2 <- evalCtsExprPlus s $ (head . tail) cs
      return $ DFPOp $ FSMMult e1 e2
  | "==" == nameOf c =
    do
      e1 <- evalCtsExprPlus s $ head cs
      e2 <- evalCtsExprPlus s $ (head . tail) cs
      return $ DFPOp $ FSMEquality e1 e2
  | "!=" == nameOf c =
    do
      e1 <- evalCtsExprPlus s $ head cs
      e2 <- evalCtsExprPlus s $ (head . tail) cs
      return $ DFPOp $ FSMInequality e1 e2
  | "<" == nameOf c =
    do
      e1 <- evalCtsExprPlus s $ head cs
      e2 <- evalCtsExprPlus s $ (head . tail) cs
      return $ DFPOp $ FSMLTTest e1 e2
  | ">" == nameOf c =
    do
      e1 <- evalCtsExprPlus s $ head cs
      e2 <- evalCtsExprPlus s $ (head . tail) cs
      return $ DFPOp $ FSMGTTest e1 e2
  | "<=" == nameOf c =
    do
      e1 <- evalCtsExprPlus s $ head cs
      e2 <- evalCtsExprPlus s $ (head . tail) cs
      return $ DFPOp $ FSMLTETest e1 e2
  | ">=" == nameOf c =
    do
      e1 <- evalCtsExprPlus s $ head cs
      e2 <- evalCtsExprPlus s $ (head . tail) cs
      return $ DFPOp $ FSMGTETest e1 e2
  | "&&" == nameOf c =
    do
      e1 <- evalCtsExprPlus s $ head cs
      e2 <- evalCtsExprPlus s $ (head . tail) cs
      return $ DFPOp $ FSMAnd e1 e2
  | "||" == nameOf c =
    do
      e1 <- evalCtsExprPlus s $ head cs
      e2 <- evalCtsExprPlus s $ (head . tail) cs
      return $ DFPOp $ FSMOr e1 e2
  | "not" == nameOf c =
    do
      e1 <- evalCtsExprPlus s $ head cs
      return $ DFPOp $ FSMNot e1
  | "&&&" == nameOf c =
    do
      e1 <- evalCtsExprPlus s $ head cs
      e2 <- evalCtsExprPlus s $ (head . tail) cs
      return $ DFPOp $ FSMBWAnd e1 e2
  | "|||" == nameOf c =
    do
      e1 <- evalCtsExprPlus s $ head cs
      e2 <- evalCtsExprPlus s $ (head . tail) cs
      return $ DFPOp $ FSMBWOr e1 e2
  | "bwnot" == nameOf c =
    do
      e1 <- evalCtsExprPlus s $ head cs
      return $ DFPOp $ FSMBWNot e1
  | "<<<" == nameOf c =
    do
      e1 <- evalCtsExprPlus s $ head cs
      e2 <- evalCtsExprPlus s $ (head . tail) cs
      return $ DFPOp $ FSMShiftL e1 e2
  | ">>>" == nameOf c =
    do
      e1 <- evalCtsExprPlus s $ head cs
      e2 <- evalCtsExprPlus s $ (head . tail) cs
      return $ DFPOp $ FSMShiftR e1 e2
  | otherwise = error $ "no general case for CtsTuple; op: " ++ (nameOf c)
{-  -- THIS IS A KLUDGE (see log 04.03.09)
  let e1 = evalCtsExprPlus s $ head cs
      e2 = evalCtsExprPlus s $ (head . tail) cs
  in
    if "+" == nameOf c
    then
      return $ DFPlus e1 e2
    else if "-" == nameOf c
    then
      return $ DFMinus e1 e2
    else error $ "no general case for tuples in evalCtsExpr"
-}

evalCtsExprPlus s (CtsSignalReq sig _) =
  case sig of
    Cont     -> return DFContReq
    GetPorts -> return DFPortsReq

evalCtsExprPlus s (CtsConstrApp c args _) =  -- see log 15.07.09 and 16.07.09
  return $ DFConstrVal c $ map (runB . (evalCtsExprPlus s)) args

evalCtsExprPlus s (CtsIfThenElse p e1 e2 _) =
  let b1 = evalCtsExprPlus s e1
      b2 = evalCtsExprPlus s e2
      c  = toGuard s p   -- see log 15.07.09
  in
    C c b1 b2

evalCtsExprPlus _ (CtsUnit _) = return DFUnit

evalCtsExprPlus s x = error $ "in evalCtsExprPlus: no case for " ++ (show x)

--
-- translate an expression into a BoolGuard:
--

toGuard :: KStatePlus -> CtsExpr -> BoolGuard
toGuard s (CtsInfixApp e1 op e2 _)
  | "==" == op  = BGEquality
                    (runB $ evalCtsExprPlus s e1)
                    (runB $ evalCtsExprPlus s e2)
  | "!=" == op  = BGInequality
                    (runB $ evalCtsExprPlus s e1)
                    (runB $ evalCtsExprPlus s e2)
  | "<" == op  = BGLT
                    (runB $ evalCtsExprPlus s e1)
                    (runB $ evalCtsExprPlus s e2)
  | ">" == op  = BGGT
                    (runB $ evalCtsExprPlus s e1)
                    (runB $ evalCtsExprPlus s e2)
  | "&&" == op = BGConjunct
                   (toGuard s e1)
                   (toGuard s e2)
  | "||" == op = BGDisjunct
                   (toGuard s e1)
                   (toGuard s e2)
  | otherwise   = error $ op ++ " is not a valid boolean guard\n"
toGuard s (CtsApp op [e1, e2] _)
  | "==" == op  = BGEquality 
                    (runB $ evalCtsExprPlus s e1)
                    (runB $ evalCtsExprPlus s e2)
  | "!=" == op  = BGInequality
                    (runB $ evalCtsExprPlus s e1)
                    (runB $ evalCtsExprPlus s e2)
  | "<" == op  = BGLT
                    (runB $ evalCtsExprPlus s e1)
                    (runB $ evalCtsExprPlus s e2)
  | ">" == op  = BGGT
                    (runB $ evalCtsExprPlus s e1)
                    (runB $ evalCtsExprPlus s e2)
  | "&&" == op = BGConjunct
                   (toGuard s e1)
                   (toGuard s e2)
  | "||" == op = BGDisjunct 
                   (toGuard s e1)
                   (toGuard s e2)
  | otherwise   = error $ op ++ " is not a valid boolean guard\n"

toGuard s (CtsApp op [e] _) 
  | "not" == op = BGNegate (toGuard s e)
  | otherwise   = error $ op ++ " is not a valid boolean guard\n"

toGuard s (CtsVar x _) = BGVar x

toGuard s (CtsConstrApp x [] _) = BGVar x

toGuard _ (CtsLitExpr (CtsLitBool b) _) = BGConstant b
-- this case is a little hacky;
-- just part of the push to finish SecureQ (2009.11.16 Schulz)
toGuard s e@(CtsTuple [op, e1, e2] _) 
  | "==" == (nameOf op) = BGEquality
                            (runB $ evalCtsExprPlus s e1)
                            (runB $ evalCtsExprPlus s e2)
  | "!=" == (nameOf op) = BGInequality
                            (runB $ evalCtsExprPlus s e1)
                            (runB $ evalCtsExprPlus s e2)
  | "<" == (nameOf op) = BGLT
                           (runB $ evalCtsExprPlus s e1)
                           (runB $ evalCtsExprPlus s e2)
  | ">" == (nameOf op) = BGGT
                           (runB $ evalCtsExprPlus s e1)
                           (runB $ evalCtsExprPlus s e2)
  | "<=" == (nameOf op) = BGLTE
                            (runB $ evalCtsExprPlus s e1)
                            (runB $ evalCtsExprPlus s e2)
  | ">=" == (nameOf op) = BGGTE
                            (runB $ evalCtsExprPlus s e1)
                            (runB $ evalCtsExprPlus s e2)
  | "&&" == (nameOf op) = BGConjunct
                            (toGuard s e1)
                            (toGuard s e2)
  | "||" == (nameOf op) = BGDisjunct
                            (toGuard s e1)
                            (toGuard s e2)
toGuard s e@(CtsTuple [op, e1] _) 
  | "not" == (nameOf op) = BGNegate (toGuard s e1)
  | otherwise  = error $ (show op) ++
                         " is not a valid boolean guard in expression: \n"
                         ++ (show e)
toGuard _ e = error $ (show e) ++ " is not a valid boolean guard\n"


--             --
-- BOILERPLATE --
--             --

nameOf :: CtsExpr -> CtsIdent
nameOf (CtsVar x _)         = x
nameOf (CtsConstrApp x _ _) = x

toInt :: DefunVal -> Int
toInt (DFInt n) = n
toInt x = error $ "in toInt: " ++ (show x)

--                               --
-- (DE)CONSTRUCT 'get' AND 'put' --
--                               --

--
-- 'put' and 'get' are yielded by application
-- in the abstract expression syntax;
-- in particular, they should appear as:
--
--   CtsApp getNameK [ ] TyMonadic "K" a
--
--   CtsApp putNameK [ ] TyMonadic "K" ( )
--
-- where "Name" is a valid CtsIdent
--
-- 29.01.09 Schulz


--
-- retrieve the component specifier from a "get" application
--
specGet :: CtsExpr -> CtsIdent
specGet (CtsApp f _ _) = init . (drop 3) $ f

--
-- retrieve component specifer from a "put" application
--
specPut :: CtsExpr -> CtsIdent
specPut (CtsApp f _ _) = init . (drop 3) $ f

--
-- retrieve the expression from a "put" application
--
exprPut :: CtsExpr -> CtsExpr
exprPut (CtsApp _ [expr] _) = expr
exprPut e = error $ "'put' expression " ++ show e
                    ++ " has wrong number of arguments"

--
-- retrieve the expression from a "get" application
--
exprGet :: CtsExpr -> CtsExpr
exprGet (CtsApp _ [expr] _) = expr
exprGet e = error $ "'get' expression " ++ show e
                    ++ " has wrong number of arguments"

-- end 'get' and 'put' --

--
-- reconstruct a literal as a value
--
ctsLitToVal :: CtsLit -> DefunVal
ctsLitToVal (CtsLitInt i)  = DFInt i
ctsLitToVal (CtsLitBool b) = DFBool b


--
-- negate an integer
--
dfvNeg :: DefunVal -> DefunVal
dfvNeg (DFInt n) = DFInt (-n)


--
-- sum two integers
--
{-
dfvSum :: DefunVal -> DefunVal -> DefunVal
dfvSum (DFInt x) (DFInt y) = DFInt (x + y)
-}

--
-- subtract two integers
--
{-
dfvSub :: DefunVal -> DefunVal -> DefunVal
dfvSub (DFInt x) (DFInt y) = DFInt (x - y)
-}

-- end boilerplate --

--          --
-- PATTERNS --
--          --

--
-- match a pattern to an expression
--

--
-- PLEASE NOTE:
--
-- all references to the CtsPVar and CtsPWildCard constructors
-- have been commented out, since these have been
-- removed from the abstract syntax.
--
-- we have left the code otherwise intact, in case
-- these patterns are reinstituted
--
-- 03.02.09 Schulz
--

ctsPMatch :: CtsExpr -> CtsPat -> Bool
-- ctsPMatch _ (CtsPVar _) = True
ctsPMatch (CtsConstrApp c1 args1 _) (CtsPConstr c2 args2) =
  (c1 == c2) && (length args1 == length args2)
ctsPMatch (CtsTuple _ _) (CtsPTuple _) = True
-- ctsPMatch _ CtsPWildCard = True
ctsPMatch _ _            = False

--
-- match a case alternative to an expression
--

ctsAltMatch ::  CtsExpr -> CtsAlt -> Bool
ctsAltMatch e (CtsAlt p _) = ctsPMatch e p

--
-- bind the parameters in a pattern to their corresponding
-- values in a matching expression
--

{-

--
-- shut off while working to avoid extraneous type conflicts
--
-- 20.07.09 Schulz
--
pBindLocal :: CtsExpr -> KState -> CtsPat -> KState
pBindLocal (CtsConstrApp c1 args1 _) env (CtsPConstr c2 args2) =
  let vals = map (evalCtsExpr env) args1
  in
    zip args2 vals
pBindLocal (CtsTuple xs _) env (CtsPTuple ys) =
  let vals = map (evalCtsExpr env) xs
  in
    zip ys vals
-- pBindLocal expr env (CtsPVar x) =
--   let y = evalCtsExpr env expr
--   in
--     [(x, y)]
-- pBindLocal _ _ _ CtsPWildCard = [ ]
pBindLocal _ _ _ = error $ "attempt to bind pattern paramters to a " ++
                             "non-matching expression"
-}


--
-- adapted to use conditional values:
--
-- 16.07.09 Schulz
--
pBindLocalPlus :: CtsExpr -> KStatePlus -> CtsPat -> KStatePlus
pBindLocalPlus (CtsConstrApp c1 args1 _) env (CtsPConstr c2 args2) =
  let vals = map (evalCtsExprPlus env) args1
  in
    zip args2 vals
pBindLocalPlus (CtsTuple xs _) env (CtsPTuple ys) =
  let vals = map (evalCtsExprPlus env) xs
  in
    zip ys vals

-- end patterns --


--                              --
-- ABSTRACT FUNCTION OPERATIONS --
--                              --

fParams :: ([CtsIdent], CtsExpr) -> [CtsIdent]
fParams = fst

fBody :: ([CtsIdent], CtsExpr) -> CtsExpr
fBody = snd

-- end abstract functions --


-- THIS IS THE END OF THE FILE --
