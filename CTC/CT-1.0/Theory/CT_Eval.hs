--
-- this is ~/cheapthreads/CTC/CT-1.0/Theory/CT_Interp.hs
--
-- a definitional interpreter for CT
--
-- put here 2010.08.02
--
-- Schulz
--

module CT_Eval where

type Ident = String

type Mem = [(Ident, Val)]

type Env = [(Ident, Val)]


--
-- first, a simplified syntax:
--

data CT = App CT CT
        | Lam Ident CT
        | ITE CT CT CT
        | Case CT [(Pat, CT)]

        | Bind_R CT CT
        | NullBind_R CT CT
        | Return_R CT
        | Step_R CT
        | Loop_R CT
        | Break_Re CT

        | Bind_Re CT CT
        | NullBind_Re CT CT
        | Return_Re CT
        | Step_Re CT
        | Loop_Re CT
        | Break_R CT

        | Bind_K CT CT
        | NullBind_K CT CT
        | Return_K CT
        | Get Ident
        | Put Ident CT

        | Add CT CT
        | Sub CT CT
        | And CT CT
        | Or CT CT
        | Var Ident
        | Lit_I Int
        | Lit_B Bool
        | Lit_Unit


data Pat = PLit_I Int
         | PLit_B Bool
         | PVar Ident
         | PPause Pat
         | PDone Pat
         | Wildcard


--
-- expressible values are monads:
--

-- resumption:
data (Monad m) => ResT m a = Done a | Pause (m (ResT m a))

instance (Monad m) => Monad (ResT m)  where
  return v         = Done v
  (Done v) >>= f   = f v
  (Pause m) >>= f  = Pause (m >>= \r -> return (r >>= f))

step_R :: (Monad m) => m a -> ResT m a
step_R x = Pause (x >>= return . return)


lift_R :: (Monad m) => m a -> ResT m a
lift_R x = Pause (x >>= return . return)


data Z a = Continue a | Break a

break_R :: (Monad m) => a -> ResT m (Z a)
break_R v = return (Break v)

loop_R r = r >>= \v -> case v of
                         (Break v)    -> return v
                         (Continue v) -> loop_R r



-- reactive resumption:
data Monad m => ReactT q r m a = D a | P (q, r -> (m (ReactT q r m a)))
                                         
instance Monad m => Monad (ReactT q r m) where
    return v      = D v
    D v >>= f     = f v
    P (q,r) >>= f = P (q, \rsp -> (r rsp) >>= \m -> return (m >>= f))  


data Req = Cont

data Rsp = Ack

step_Re :: (Monad m) => m a -> ReactT Req Rsp m a
step_Re x = P (Cont, \Ack -> x >>= (return . return))


lift_Re :: (Monad m) => m a -> ReactT Req Rsp m a
lift_Re x = P (Cont, \Ack -> x >>= (return . return))


type Re a = ReactT Req Rsp (StateT Mem Id) a


loop_Re r = r >>= \v -> case v of
                          (Break v)    -> return v
                          (Continue v) -> loop_R r


break_Re :: (Monad m) => a -> ReactT Req Rsp m (Z a)
break_Re v = return (Break v)


-- state:
data (Monad m) => StateT s m a = ST (s -> m (a, s))
prj_ST (ST s) = s

instance (Monad m) => Monad (StateT s m) where
  return x      = ST (\s -> return (x, s))
  (ST s) >>= f  = ST (\s' -> (s s') >>= \(x, s'') -> (prj_ST (f x)) s'')


lift_ST :: Monad m => m a -> StateT s m a
lift_ST x = ST (\s -> x >>= \v -> return (v, s))


upd :: (Monad m) => (s -> s) -> StateT s m ()
upd f = ST (\s -> return ((), f s))

get :: (Monad m) => StateT s m s
get = ST (\s -> return (s, s))


-- the identity:
data Id a = Id a

instance Monad Id where
  return x      = Id x
  (Id x) >>= f  = f x


type R a = ResT (StateT Mem Id) a

type K a = StateT Mem Id a



--
-- expressible values:
--
data Val = RES (R Val)
         | REACT (Re Val)
         | CODE (K Val)
         | FUN Ident CT
         | CL Ident CT Env
         | BREAK Val
         | INT Int
         | BOOL Bool
         | Unit


--
-- auxiliaries of the environment:
--
lkp :: Env -> Ident -> Val
lkp ((y,v):e) x = if x == y then v else lkp e y

extenv :: Env -> Ident -> Val -> Env
extenv e x v = (x,v):e


--
-- a monadic evaluator:
--

eval_any :: Env -> CT -> Val

eval_any e (Var x)   = lkp e x

eval_any e (Lam x p) = (CL x p e)

--
-- switching among first-class monadic values:
--

eval_any e (Bind_R r r')      = RES (eval_R e (Bind_R r r'))
eval_any e (NullBind_R r r')  = RES (eval_R e (NullBind_R r r'))
eval_any e (Return_R x)       = RES (eval_R e (Return_R x))
eval_any e (Step_R k)         = RES (eval_R e (Step_R k))
eval_any e (Loop_R r)         = RES (eval_R e (Loop_R r))

eval_any e (Bind_Re r r')     = REACT (eval_Re e (Bind_Re r r'))
eval_any e (NullBind_Re r r') = REACT (eval_Re e (NullBind_Re r r'))
eval_any e (Return_Re x)      = REACT (eval_Re e (Return_Re x))
eval_any e (Step_Re k)        = REACT (eval_Re e (Step_Re k))
eval_any e (Loop_Re r)        = REACT (eval_Re e (Loop_Re r))

eval_any e (Bind_K r r')      = CODE (eval_K e (Bind_K r r'))
eval_any e (NullBind_K r r')  = CODE (eval_K e (NullBind_K r r'))
eval_any e (Return_K x)       = CODE (eval_K e (Return_K x))
eval_any e (Get x)            = CODE (eval_K e (Get x))
eval_any e (Put x v)          = CODE (eval_K e (Put x v))

--
-- default to primitive evaluation:
--
eval_any e x = (\(Id x) -> x) (eval_I e x)




--
-- evaluation of the top-level execution stream:
--
eval_R :: Env -> CT -> R Val


eval_R e (App f x)    = let v            = eval_any e x
                            (CL x' p e') = eval_any e f
                            e''          = extenv e' x' v
                        in
                          eval_R e'' p


eval_R e (Var x)      = case (lkp e x) of
                          (RES r) -> r
                          v       -> return v


eval_R e (ITE b p p') = (step_R . lift_ST) (eval_I e b) >>= \(BOOL b') ->
                        if b' then (eval_R e p) else (eval_R e p')


eval_R e (Bind_R r r') = eval_R e r >>= \v ->
                         eval_R e r' >>= \(CL x p e') ->
                         let e'' = extenv e' x v
                         in
                           eval_R e'' p


eval_R e (NullBind_R r r') = (eval_R e r) >> (eval_R e r')


eval_R e (Return_R x) = return (eval_any e x)


eval_R e (Step_R x) = step_R (eval_K e x)


eval_R e (Loop_R r) = loop_R
                      ( 
                        eval_R e r >>= \v ->
                        case v of
                          (BREAK v') -> return (Break v')
                          _          -> return (Continue v)

                      )

eval_R e (Break_R x) = (step_R . lift_ST . Id) (eval_any e x) >>= \v ->
                       return (BREAK v)


--
-- evaluation of user threads:
--
eval_Re :: Env -> CT -> Re Val


eval_Re e (App f x)    = let v            = eval_any e x
                             (CL x' p e') = eval_any e f
                             e''          = extenv e' x' v
                         in
                           eval_Re e'' p


eval_Re e (Var x)   = return (lkp e x)


eval_Re e (ITE b p p') = (lift_Re . lift_ST) (eval_I e b) >>= \(BOOL b') ->
                         if b' then (eval_Re e p) else (eval_Re e p')


eval_Re e (Bind_Re r r') = eval_Re e r >>= \v ->
                           eval_Re e r' >>= \(CL x p e') ->
                           let e'' = extenv e' x v
                           in
                             eval_Re e'' p


eval_Re e (NullBind_Re r r') = (eval_Re e r) >> (eval_Re e r')


eval_Re e (Return_Re x) = return (eval_any e x)


eval_Re e (Step_Re x) = step_Re (eval_K e x)


eval_Re e (Loop_Re r) = loop_Re
                        ( 
                          eval_Re e r >>= \v ->
                          case v of
                            (BREAK v') -> return (Break v')
                            _          -> return (Continue v)
                        )

eval_Re e (Break_Re x) = (lift_Re . lift_ST . Id) (eval_any e x) >>= \v ->
                         return (BREAK v)



--
-- evaluation of the state component:
--
eval_K :: Env -> CT -> K Val


eval_K e (App f x)    = let v            = eval_any e x
                            (CL x' p e') = eval_any e f
                            e''          = extenv e' x' v
                        in
                          eval_K e'' p


eval_K e (Var x)   = return (lkp e x)


eval_K e (Bind_K k k') = eval_K e k >>= \v ->
                         eval_K e k' >>= \(CL x p e') ->
                         let e'' = extenv e' x v
                         in
                           eval_K e'' p


eval_K e (NullBind_K k k') = eval_K e k >> eval_K e k'


eval_K e (Return_K p) = return (eval_any e p)


eval_K e (Get x)   = get >>= \m -> return (lkp m x)


eval_K e (Put x p) = let (Id v') = eval_I e p
                     in
                       upd
                       (\m ->
                         map (\(y, v) -> if y == x then (y, v') else (y, v)) m)

                       >> return Unit


eval_K e (ITE b p p') = lift_ST (eval_I e b) >>= \(BOOL b') ->
                        if b' then (eval_K e p) else (eval_K e p')



--
-- evaluation of simply expressible values:
--
eval_I :: Env -> CT -> Id Val

eval_I e (Var x)   = return (lkp e x)

eval_I e (Add n m) = eval_I e n >>= \(INT v) ->
                     eval_I e m >>= \(INT v') ->
                     return (INT (v + v'))

eval_I e (Sub n m) = eval_I e n >>= \(INT v) ->
                     eval_I e m >>= \(INT v') ->
                     return (INT (v - v'))

eval_I e (And x y) = eval_I e x >>= \(BOOL b) ->
                     eval_I e y >>= \(BOOL b') ->
                     return (BOOL (b && b'))

eval_I e (Or x y)  = eval_I e x >>= \(BOOL b) ->
                     eval_I e y >>= \(BOOL b') ->
                     return (BOOL (b || b'))

eval_I _ (Lit_I n) = return (INT n)
eval_I _ (Lit_B b) = return (BOOL b)
eval_I _ Lit_Unit  = return Unit



{-
eval :: Env -> CT -> R Val
eval e (App f x)    = eval e x >>= \v ->
                      eval e f >>= \(CL x p e') ->
                      let e'' = extenv e' x v
                      in
                        eval e'' p


eval e (Lam x p)    = return (CL x p e)



eval e (Case o as)  = eval e o >>= \v ->
                      let (e', p) = match v as
                      in
                        eval (e' ++ e) p


eval e (Var x)      = return (lkp e x)


eval e (Bind p p')  = eval e p >>= \v ->
                      eval e p' >>= \(CL x p'' e') ->
                      let e'' = extenv e' x v
                      in
                        eval e'' p''


eval e (NullBind p p') = (eval e p) >> (eval e p')


eval e (Return p) = eval e p



match :: Val -> [(Pat, CT)] -> (Env, CT)
match _ _ = ([], Lit_Unit)
-}

-- THIS IS THE END OF THE FILE --
