--
-- this is ~/cheapthreads/CTC/CT-1.0/RPSLam/Targets/Interp.hs
--
-- a definitional interpreter for the target language for the
-- RPS demonstration compiler
--
-- put here 2010.12.31
--
-- Schulz
--

module Targets.Interp where

import Compile.Constants

import Targets.Syntax
import PPT

import MonadicConstructions

import Data.List

import Debug

type Env = [(Ref, TVal)]

type EnvStack = [Env]

type VarStack = [TVal]

type CallStack = [Code]

type Mem = [(Ref, TVal)]

type M a = StateT ((((EnvStack, VarStack), Mem), CallStack), Prog) Id a


--                --
-- TOP-LEVEL CALL --
--                --
interp_obj :: Prog -> TVal
interp_obj p@(Prog ps) =

--  let mn = actlkp mainl ps
  let mn = actlkp handler ps
  in

    -- result value should appear in the monadic return register:
    prj p (interp_code mn >> mread R_Ret >>= \(Just v) -> return v)
--    prj p (interp_code mn >> mread (Var "m") >>= \(Just v) -> return v)


--                  --
-- BASIC OPERATIONS --
--                  --

prj :: Prog -> M a -> a
prj (Prog p) m =

  let dn = Seq (Halt (DeRef R_Ret)) End
  in
    (fst . deId) ((deST m) (((([initenv], []), []), [dn]), (Prog p)))

{-
  let dn = Seq (Halt (DeRef R_Ret)) End
      hn = actlkp handler p
  in
    (fst . deId) ((deST m) (((([initenv], []), []), [hn, dn]), (Prog p)))
-}


lkp :: String -> M TVal
lkp x = get >>= \(((((e:_), _), _), _), _) ->
        case (lookup (Var x) e) of
          (Just v) -> return v
          Nothing  -> error $ "variable not in scope: " ++ x


mread :: Ref -> M (Maybe TVal)

mread r =

  case r of
    (StructFld r' x) -> mread r' >>= \u ->
                        case u of
                          (Just (ConV _ xs))   -> case (lookup x xs) of
                                                    (Just v) -> return (Just v)
                                                    Nothing  -> return Nothing


                          (Just v)             -> return $ Just $ Error $
                                                  "no fields in " ++ (ppt v)
                                                  ++ "; looked for " ++ x

                          Nothing              -> return Nothing

    r                -> get >>= \(((_, m), _), _) ->
                        return (lookup r m)



write :: Ref -> TVal -> M ()
write r v =

  case r of

    (StructFld r' x) -> mread r' >>= \u ->
                        case u of

                          -- if r' exists, replace the relevant field
                          (Just (ConV c xs)) -> let xs' = deleteBy 
                                                            (\x -> \y ->
                                                            (fst x) == (fst y))
                                                          (x, WrongT) xs

                                                    u'  = ConV c ((x, v):xs')
                                                in
                                                  write r' u'
                                                  
                                                  

                          (Just Nil)         -> write r' (ConV "" [(x, v)])

                          (Just v)           -> error $
                                                "failed to write field " ++ x
                                                ++ " in " ++ (ppt r)

                          -- if r' has not yet been written, create it
                          -- and write the field
                          Nothing            -> get >>= \(((_, m), _), _) ->
                                                let m' = deleteBy
                                                         (\x -> \y ->
                                                           (fst x) == (fst y))
                                                          (r, WrongT) m

                                                    v' = ConV "var" [(x, v)]
                                                in
                                                  write r' v'

    r                -> get >>= \(((_, m), _), _) ->
                        let m' = deleteBy
                                   (\x -> \y -> (fst x) == (fst y)) (r, v) m
                        in
                          upd (\(((s, _), p), g) -> (((s, (r, v):m'), p), g))




pushe :: Env -> M ()
pushe e = upd (\((((es, vs), m), ps), s) -> ((((e:es, vs), m), ps), s))
          

pope ::  M Env
pope = get >>= \((((e:es, vs), m), ps), s) ->
       put ((((es, vs), m), ps), s) >>
       return e


tope ::  M Env
tope = get >>= \((((e:_, _), _), _), _) ->
       return e


pushv :: TVal -> M ()
pushv v = upd (\((((e, vs), m), ps), s) -> ((((e, v:vs), m), ps), s))


popv :: M TVal
popv = get >>= \((((e, v:vs), m), ps), s) ->
       put ((((e, vs), m), ps), s) >>
       return v


push :: Code -> M ()
push p = get >>= \((m, ps), s) ->
         put ((m, p:ps), s)


pop :: M Code
pop = get >>= \((m, p:ps), s) ->
      put ((m, ps), s) >>
      return p


jump :: Label -> M ()
jump l = get >>= \(_, (Prog p)) ->
         interp_code (actlkp l p)

actlkp :: Label -> [Act] -> Code
actlkp l ((Act l' p):as) = if l == l' then p
                           else case (labellkp l p) of
                                  (Just p') -> p'
                                  Nothing   -> actlkp l as

actlkp l _ = error $ "couldn't locate label: " ++ l


labellkp :: Label -> Code -> Maybe Code
labellkp l (Labeled l' p) = if l == l'
                            then Just (Labeled l' p)
                            else labellkp l p

labellkp l (Seq _ p)      = labellkp l p
labellkp l End            = Nothing



mdump :: (Show a) => M a
mdump = get >>= \((((_, _), m), _), _) ->
        return (error $ show m)



--              --
-- INTERPRETERS --
--              --



interp_code :: Code -> M ()
interp_code (Labeled _ p)    = interp_code p
--interp_code (Labeled l p)    = (dbtrace l (return ())) >> interp_code p

interp_code (Seq (JSR r) p)  = mread r >>= \v ->
                                 case v of
                                   (Just (LabelT l)) -> push p >> jump l
                                   -- (Just (LabelT l)) -> dbtrace ("push: " ++ (take 20 (show p))) (push p) >> jump l

{-
                                   (Just (Error x))  -> error $ x ++ " at\n"
                                                        ++ (ppt i)
-}

                                   (Just _)          -> error $ "jump to: "
                                                        ++ (show v)

                                   Nothing           -> error $ "jump given by"
                                                        ++ " unbound variable "
                                                        ++ (ppt r)

interp_code (Seq (JSRI l) p) = push p >> jump l
--interp_code (Seq (JSRI l) p) = dbtrace ("push: " ++ (take 20 (show p))) (push p) >> jump l

interp_code (Seq Return _)   = pop >>= \p -> interp_code p
--interp_code (Seq Return _)   = pop >>= \p -> dbtrace ("return to: " ++ (take 20 (show p))) (interp_code p)

interp_code (Seq (Jmp r) _)  = mread r >>= \v ->
                                 case v of

                                   (Just (LabelT l)) -> jump l
--                                   (Just (LabelT l)) -> dbtrace l (jump l)

{-
                                   (Just (Error x))  -> error $ x ++ " at\n"
                                                        ++ (ppt i)
-}

                                   (Just _)          -> error $ "jump to: "
                                                        ++ (show v)

                                   Nothing           -> error $ "jump given by"
                                                        ++ " unbound variable "
                                                        ++ (ppt r)


interp_code (Seq (JmpI l) _) = jump l
--interp_code (Seq (JmpI l) _) = dbtrace l (jump l)


interp_code (Seq (BZ x l) p) = eval x >>= \v ->
                               case v of
                                 (BolT False) -> jump l
                                 (BolT True)  -> interp_code p
--                                 (BolT False) -> dbtrace l (jump l)
--                                 (BolT True)  -> dbtrace (ppt x) (interp_code p)
                                 _            -> error $
                                                   "branch to: " ++ (show v)

interp_code (Seq (Halt x) _) = eval x >>= \v ->
                               write R_Ret v

interp_code (Seq s p)        = interp_stmt s >> interp_code p

interp_code End              = return ()



interp_stmt :: Stmt -> M ()

interp_stmt (Assign r v) = eval v >>= \v' ->
--                           dbtrace (ppt (Assign r (Con v'))) (return ()) >>
                           write r v'

interp_stmt (Push x)     = eval x >>= \v' ->
                           pushv v'

interp_stmt (Pop r)      = popv >>= \v ->
                           write r v

interp_stmt i@(PushEnv x)  = eval x >>= \v ->
                             case v of
                               (EnvT e)  -> pushe e
                               (Error x) -> error $ x ++ " at " ++ (ppt i)
                               _         -> error $ "malformed environment: "
                                            ++ (show v)

interp_stmt PopEnv       = pope >> return ()

interp_stmt (LkpV x)     = mread (Var x) >>= \x' -> 
                           case x' of
                             (Just (NameT x'')) -> lkp x'' >>= \v ->
                                                   -- dbtrace (x'' ++ " = " ++ (show v)) (return ()) >>
                                                   write R_Ret v

                             v                  -> error $ "lookup failed: "
                                                   ++ (show (x, v))

interp_stmt Nop          = return ()




eval :: TExpr -> M TVal
eval (Inc x)   = eval x >>= \v ->
                 case v of
                   (NumT n)  -> return (NumT (n + 1))
                   (Error x) -> return (Error x)
                   _         -> error $ "in eval:" ++ (show x)
     
eval (Dec x)   = eval x >>= \v ->
                 case v of
                   (NumT n)  -> return (NumT (n - 1))
                   (Error x) -> return (Error x)
                   _         -> error $ "in eval:" ++ (show x)


eval (IsNumT x)  = eval x >>= \v ->
                   case v of
                     (NumT _)       -> return (BolT True)
                     (ConV "Num" _) -> return (BolT True)
                     (Error x)      -> return (Error x)
                     _              -> return (BolT False)

eval (IsBoolT x)  = eval x >>= \v ->
                    case v of
                      (BolT _)        -> return (BolT True)
                      (ConV "Bool" _) -> return (BolT True)
                      (Error x)       -> return (Error x)
                      _               -> return (BolT False)

eval (IsClT x)    = eval x >>= \v ->
                    case v of
                     (ConV "Cl" _) -> return (BolT True)
                     (ClT _ _ _)   -> return (BolT True)
                     (Error x)     -> return (Error x)
                     _             -> return (BolT False)

eval (IsRecClT x) = eval x >>= \v ->
                    case v of
                      (ConV "RecCl" _) -> return (BolT True)
                      (RecClT _ _ _)   -> return (BolT True)
                      (Error x)        -> return (Error x)
                      _                -> return (BolT False)


eval (And x y) = eval x >>= \v ->
                 eval y >>= \u ->
                   case (u, v) of
                     (BolT b, BolT b') -> return (BolT (b && b'))
                     (Error x, _)      -> return (Error x)
                     (_, Error y)      -> return (Error y)
                     _                 -> error $ "in eval" ++ (show x)

eval (Or x y)  = eval x >>= \v ->
                 eval y >>= \u ->
                 case (u, v) of
                   (BolT b, BolT b') -> return (BolT (b && b'))
                   (Error x, _)      -> return (Error x)
                   (_, Error y)      -> return (Error y)
                   _                 -> error $ "in eval" ++ (show x)


eval (EqTst x y) = eval x >>= \u ->
                   eval y >>= \v ->
--                   dbtrace (ppt x ++ " == " ++ ppt y) (return ()) >>
--                   dbtrace (ppt u ++ " == " ++ ppt v) (return ()) >>
                   return (BolT (u == v))


eval (DeRef (RR r)) =

  mread (Var r) >>= \v'' ->

  let isres r = case r of
                  (Just (LabelT _)) -> True
                  (Just (ConV _ _)) -> True
                  _                 -> False
  in

  if (not (isres v'')) then eval (DeRef (Var r)) else

  -- save the current contents of the affected registers
  mread R_Nxt >>= \(Just nx) ->
  mread R_Req >>= \(Just rq) ->
  mread R_Done >>= \(Just dn) ->
  mread R_Ret >>= \(Just rt) ->

  mread (Var r) >>= \l ->

  (
    case l of

      (Just (LabelT l')) -> interp_code (Seq (JSRI l') End) >>
                            mread R_Nxt >>= \(Just nx') ->
                            mread R_Req >>= \(Just rq') ->
                            mread R_Done >>= \(Just dn') ->
                            mread R_Ret >>= \(Just rt') ->

                            write R_Nxt nx >>
                            write R_Req rq >>
                            write R_Done dn >>
                            write R_Done rt >>

                            return (nx', rq', dn', rt')

      (Just (ConV _ xs)) -> let (Just nx') = lookup callfld xs
                                (Just rq') = lookup reqfld xs
                                (Just dn') = lookup donefld xs
                                (Just rt') = lookup valfld xs
                            in
                              return (nx', rq', dn', rt')


  ) >>= \(nx', rq', dn', rt') ->

  let dn'' = (donefld, dn')
      rq'' = (reqfld, rq')
      nx'' = (callfld, nx')
      rt'' = (valfld, rt')
      rv   = ConV "RER" [dn'', rq'', nx'', rt'']
  in
    return rv
  



-- 'main' is obviously a reserved keyword that always points
-- to the entry point of the program; this really just provides an expedient
-- way to initialize the handler loop.
--
-- (2011.01.13) Schulz
--
eval (DeRef (Var "main")) = return (LabelT mainl)

eval (DeRef r) = mread r >>= \v ->
                 case v of
                   (Just v) -> return v
                   Nothing  -> return Nil


eval TopEnv        = tope >>= \e -> return (EnvT e)

eval (TxEnv h x v) = eval v >>= \v' ->
                     eval x >>= \(NameT x') ->
                     eval h >>= \h' ->
                     -- dbtrace ("**" ++ show (x', v')) (return ()) >>
                     case h' of
                       (EnvT rho) -> return (EnvT (((Var x'), v'):rho))
                       (Error x)  -> return (Error x)
                       _          -> error $ "in eval " ++ (show h')


eval (ConX c xs) =

  (foldr
    (\(f, x) -> \m -> eval x >>= \v -> m >>= \vs -> return ((f, v):vs))
      (return []) xs
  ) >>= \vs ->

  return (ConV c vs)


eval (VX v)        = return v


 


--                            --
-- BOILERPLATE AND MISCELLANY --
--                            --


--
-- get the base variable from a structure field reference
-- (since structures may be nested):
--
baseref :: Ref -> Ref
baseref (StructFld r _) = baseref r
baseref r = r





-- THIS IS THE END OF THE FILE --
