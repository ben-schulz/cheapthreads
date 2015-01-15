--
-- this is ~/cheapthreads/ctc_working/CT-1.0/RPSLam/interpreters/InterpRSI.hs
--
-- a monadic-style interpreter for PCF;
--
-- iteration four: simulating the environment monad using a layered
-- resumption-state monad;
--
-- Note that this allows the removal of explicit environment arguments,
-- as in the first introduction (iteration two) of the environment monad.
--
-- put here (2010.12.06)
--
-- Schulz
--

module Interpreters.InterpRSI where

import Prelude 

import PCF.Syntax
import MonadicConstructions

--
-- values in the factored reactive interpreter;
--
-- note that pure functions have been replaced by closures,
-- reflecting the removal of the environment monad;
--
data V_Re = Wrong 
          | Num Int
          | Bol Bool
          | Cl Name Env (Re V_Re)
          | RecCl Name Env (Re V_Re)


instance Show V_Re where
    show Wrong         = "Wrong"
    show (Num i)       = show i
    show (Bol b)       = show b
    show (Cl _ _ _)    = "<closure>"
    show (RecCl _ _ _) = "<recclosure>"

type Env = [(Name, V_Re)]

data Req = Cont
         | MkCl Name (Re V_Re)
         | MkRecCl Name (Re V_Re)
         | Ap V_Re V_Re
         | AppEnv Name


data Rsp = Ack
         | Val V_Re

type R a = ResT (StateT [Env] Id) a

type Re a = ReactT Req Rsp Id a


rdEnv_R :: R Env
rdEnv_R = step_R get >>= \(rho:_) -> return rho

inEnv_R :: Env -> R a -> R a
inEnv_R rho r = step_R (upd (\es -> rho:es)) >>
               r >>= \v ->
               step_R (upd tail) >>
               return v

--resume :: (Rsp -> Re V_Re) -> Rsp -> R (Re V_Re)
resume r rsp = step_R (liftSt (r rsp))


sched :: (Re V_Re -> R (Re V_Re)) -> Re V_Re -> R V_Re
sched f (D v) = Done v
sched f phi   = f phi >>= \phi' -> sched f phi'


exec :: Re V_Re -> R V_Re
exec t = sched hand t


hand :: Re V_Re -> R (Re V_Re)
hand (P (Cont, r))                 = resume r Ack

hand (P (MkCl x phi, r))           = rdEnv_R >>= \rho ->
                                     resume r (Val (Cl x rho phi)) 

hand (P (MkRecCl x phi, r))        = rdEnv_R >>= \rho ->
                                     let rho' = xEnv rho x (RecCl x rho phi)
                                     in
                                       inEnv_R rho' (exec phi) >>= \v ->
                                       resume r (Val v)

hand (P (Ap (Cl x rho' phi) v, r)) = rdEnv_R >>= \rho ->
                                     let rho' = xEnv rho' x v
                                     in
                                       inEnv_R rho' (exec phi) >>= \v' ->
                                       resume r (Val v')

hand (P (Ap _ v, r))               = resume r (Val Wrong)


hand (P (AppEnv x, r))     = rdEnv_R >>= \rho ->
                             case (lkp x rho) of

                             -- recursive call:
                             (RecCl x rho' phi) -> let rho'' = xEnv rho' x
                                                               (RecCl x rho phi)
                                                   in
                                                     inEnv_R rho''
                                                       (exec phi) >>= \v ->
                                                     resume r (Val v)

                             -- any other value:
                             v                  -> resume r (Val v)


hand (D v)                 = return (D v)


--
-- the interpreter:
--

initenv = []

interp_rsi :: Term -> V_Re
interp_rsi t = (fst . deId) ((deST (run_R (exec (interp t)))) [initenv])

interp :: Term -> Re V_Re
interp (Lam x t)  = mkfun x (interp t)

interp (App t t') = interp t' >>= \a ->
                    interp t >>= \f ->
                    apply f a

interp (Inc t)    = interp t >>= \v ->
                    case v of
                      (Num n) -> return (Num (n + 1))
                      _       -> return Wrong


interp (Dec t)    = interp t >>= \v -> 
                    case v of
                      (Num n) -> return (Num (n - 1))
                      _       -> return Wrong

interp (ZTest t)  = interp t >>= \v ->
                    case v of
                      (Num 0) -> return (Bol True)
                      (Num _) -> return (Bol False)
                      _       -> return Wrong

interp (EF t t' t'') = interp t >>= \b ->
                       case b of
                         (Bol False) -> interp t''
                         (Bol True)  -> interp t'
                         _           -> return Wrong

interp (Mu x t)   = mkrecfun x (interp t)

interp (Var x)    = signalV (AppEnv x)

interp (Con n)    = return (Num n)

interp (Bit b)    = return (Bol b)


--                                       --
-- Characteristic Interpreter Morphisms: --
--                                       --

signalV :: Req -> Re V_Re
signalV q = P (q, \(Val v) -> return (return v))


xEnv :: Env -> Name -> V_Re -> Env
xEnv rho x v = (x, v):rho

--
-- apply the environment:
--
lkp :: Name -> Env -> V_Re
lkp x ((y,b):bs) = if x == y then b else lkp x bs
lkp x [] = Wrong


--
-- form an application:
--
apply :: V_Re -> V_Re -> Re V_Re
apply f v = signalV (Ap f v)


--
-- create a function from an abstraction:
--
mkfun :: Name -> Re V_Re -> Re V_Re
mkfun x f = signalV (MkCl x f)

--
-- create a recursive closure:
--
mkrecfun :: Name -> Re V_Re -> Re V_Re
mkrecfun x f = signalV (MkRecCl x f)



-- THIS IS THE END OF THE FILE --
