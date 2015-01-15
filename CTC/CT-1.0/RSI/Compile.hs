--
-- this is ~/cheapthreads/CTC/CT-1.0/RSI/Compile.hs
--
-- Code generation from CT to the RSI intermediate form;
--
-- put here 2010.08.16
--
-- Schulz
--

module RSI.Compile where

import RSI.Syntax

import CT.Syntax
import CT.INAST

import CT.MonadicConstructions

import CT.PPT

import Data.Char  -- only for simple label-manipulation purposes

--                --
-- TOP LEVEL CALL --
--                --

rsi_gen :: INProg -> RSI
rsi_gen (INProg ((mn, ds), (dats, mons))) =

  let fenv = mkfenv (mn:ds)
      rho  = mkconenv fenv dats
      gds  = decglobals mons
  in
    prj_rc $

    inEnv rho $

    compile_fun mn >>= \(is, r) ->

    (foldr

      (\f -> \m ->
        compile_fun f >>= \(vs, p) ->
        m >>= \(vs', ps) ->
        return (vs ++ vs', p ++ ps)
      )

        (return ([], [])) ds
    
    ) >>= \(vs, rs) ->

    return (RSI (gds ++ is ++ vs, (funlabel program_entry, (r ++ rs))))


compile_fun :: INFunDec -> RC ([DDec], [Code])
compile_fun (INFunDec ((f, t), (xs, p))) =

  rdEnv >>= \rho ->

  let xs'  = map VBind xs
      ys   = zip xs xs'
      rho' = foldr (\(x, x') -> \e -> (\y -> if x == y then x' else e y)) rho ys

      -- make declarations for the function parameters:
      ts = zip xs (argtsof t)
      vs = map (\(x, t) -> VDec x (torsity t)) ts
  in

    case (codomof t) of
      (CTMTy ResTy _)     -> inEnv rho' (compile_R' p) >>= \(vs', (p', ps')) ->
                             genpause >>= \l ->
                             gendone >>= \l' ->
                             let rts = Jmp l (LabelRef (rtsreg f)) (Halt l')
                                 p'' = chaincat p' rts
                             in
                               return (vs ++ vs', ((R (funlabel f) p''):ps'))


      (CTMTy (ReactTy _ _) _) -> inEnv rho' (compile_Re p) >>= \(vs',(p',ps'))->
                                 genpause >>= \l ->
                                 gendone >>= \l' ->
                                 let rts = Jmp l (LabelRef (rtsreg f)) (Halt l')
                                     p'' = chaincat p' rts
                                 in
                                   return (vs ++ vs',((R (funlabel f) p''):ps'))


      (CTMTy StateTy _)   -> inEnv rho' (compile_K p) >>= \(vs', (p', ps')) ->
                             return (vs ++ vs', ((K (funlabel f) p'):ps'))

      _                   -> return ([], [])


--
-- the various compiler returns are aggregated
-- here to allow passing of resumptions, state
-- as arguments to functions
--

data Any = Res Chain
         | Sta Block
         | Idn Expr


--
-- just your usual compilation monad:
--

--
-- environment distinguishes scalars, declared functions, and resumptions:
--
type Reg = String
data Binding = VBind Reg                -- variable symbol binding
             | CBind String [Reg]       -- constructor
             | LBind Label              -- loop currently in scope
             | FBind Label [Reg] INAST  -- declared function
             | ABind INAST              -- argument to an in-scope function
             | NOBIND
             deriving Show

--
--
-- code generation monad, and its operations:
--
--

type REnv = String -> Binding

--
-- separate counters are used only because it makes the output a little
-- easier to read and understand when the different labels
-- are numbered in series
--
type Counter = (Int, Int, Int, Int, Int, Int, Int, Int, Int, Int)

type RC a = EnvT REnv (StateT Counter Id) a

prj_rc :: RC a -> a
prj_rc (ENV e) = fst $ (deId ((deST (e (initenv))) initct))


--
-- extend the environment:
--
extenv :: String -> Binding -> RC REnv
extenv x v = rdEnv >>= \rho -> return (\y -> if y == x then v else rho y)

extenv_many :: [(String, Binding)] -> RC REnv
extenv_many = foldr
                (\(x, v) -> \m -> extenv x v >>= \rho -> inEnv rho m) (rdEnv)

--
-- get the parameters bound to a declared function:
--
argsof :: String -> RC [String]
argsof f = rdEnv >>= \rho -> case (rho f) of
                               (FBind _ xs _) -> return xs

--
-- get the label bound to a function:
--
localof :: String -> RC Label
localof f = rdEnv >>= \rho -> case (rho f) of
                                (FBind l _ _) -> return l

--
-- get the code associated with a function:
--
termof :: String -> RC INAST
termof f = rdEnv >>= \rho -> case (rho f) of
                               (FBind _ _ p) -> return p

--
-- make a new variable name:
--
genvar :: RC String
genvar =

  liftEnv $

    get >>= \(_, n, _, _, _, _, _, _, _, _) ->

    upd (\(n0, n1, n2, n3, n4, n5, n6, n7, n8, n9) ->
          (n0, n1 + 1, n2, n3, n4, n5, n6, n7, n8, n9)) >>

    return (internal_var ++ (show n))

genresume :: RC String
genresume =

  liftEnv $

    get >>= \(_, _, n, _, _, _, _, _, _, _) ->
    upd (\(n0, n1, n2, n3, n4, n5, n6, n7, n8, n9) ->
          (n0, n1, n2 + 1, n3, n4, n5, n6, n7, n8, n9)) >>
    return (resume_var ++ (show n))



--
-- make a new loop label:
--
genlooplabel :: RC String
genlooplabel =

  liftEnv $

    get >>= \(_, _, _, n, _, _, _, _, _, _) ->
    upd (\(n0, n1, n2, n3, n4, n5, n6, n7, n8, n9) ->
          (n0, n1, n2, n3 + 1, n4, n5, n6, n7, n8, n9)) >>
    return (loop_label ++ (show n))

--
-- make a new resumption variable:
--
genresvar :: RC String
genresvar =

  liftEnv $

    get >>= \(_, _, _, _, n, _, _, _, _, _) ->
    upd (\(n0, n1, n2, n3, n4, n5, n6, n7, n8, n9) ->
          (n0, n1, n2, n3, n4 + 1, n5, n6, n7, n8, n9)) >>
    return (res_var ++ (show n))

--
-- make a new code label:
--
genblklabel :: RC String
genblklabel =

  liftEnv $

    get >>= \(_, _, _, _, _, n, _, _, _, _) ->
    upd (\(n0, n1, n2, n3, n4, n5, n6, n7, n8, n9) ->
          (n0, n1, n2, n3, n4, n5 + 1, n6, n7, n8, n9)) >>
    return (block_label ++ (show n))

genpause :: RC String
genpause =

  liftEnv $

    get >>= \(_, _, _, _, _, _, n, _, _, _) ->
    upd (\(n0, n1, n2, n3, n4, n5, n6, n7, n8, n9) ->
          (n0, n1, n2, n3, n4, n5, n6 + 1, n7, n8, n9)) >>
    return (pause_label ++ (show n))


gendone :: RC String
gendone =

  liftEnv $

    get >>= \(_, _, _, _, _, _, _, n, _, _) ->
    upd (\(n0, n1, n2, n3, n4, n5, n6, n7, n8, n9) ->
          (n0, n1, n2, n3, n4, n5, n6, n7 + 1, n8, n9)) >>
    return (done_label ++ (show n))


genlamlabel :: RC String
genlamlabel =

  liftEnv $

    get >>= \(_, _, _, _, _, _, _, _, n, _) ->
    upd (\(n0, n1, n2, n3, n4, n5, n6, n7, n8, n9) ->
          (n0, n1, n2, n3, n4, n5, n6, n7, n8 + 1, n9)) >>
    return (lam_label ++ (show n))

genretlabel :: RC String
genretlabel =

  liftEnv $

    get >>= \(_, _, _, _, _, _, _, _, _, n) ->
    upd (\(n0, n1, n2, n3, n4, n5, n6, n7, n8, n9) ->
          (n0, n1, n2, n3, n4, n5, n6, n7, n8, n9 + 1)) >>
    return (ret_label ++ (show n))

genback :: RC String
genback =

  liftEnv $

    get >>= \(n, _, _, _, _, _, _, _, _, _) ->
    upd (\(n0, n1, n2, n3, n4, n5, n6, n7, n8, n9) ->
          (n0 + 1, n1, n2, n3, n4, n5, n6, n7, n8, n9)) >>
    return (jumpback_label ++ (show n))



--                         --
-- MAIN COMPILER FUNCTIONS --
--                         --


--
--
compile_any :: INAST -> RC ([DDec], (Any, [Code]))

compile_any e = case (typeofinast e) of

                  (CTMTy ResTy _)         -> compile_R' e >>= \(vs, (p, ps)) ->
                                             return (vs, (Res p, ps))

                  (CTMTy (ReactTy _ _) _) -> compile_Re' e >>= \(vs, (p, ps)) ->
                                             return (vs, (Res p, ps))

                  (CTMTy StateTy _)       -> compile_K e >>= \(vs, (p, ps)) ->
                                             return (vs, (Sta p, ps))

                  _                       -> compile_I e >>= \(vs, (e', ps)) ->
                                             return (vs, (Idn e', ps))


--                   --
-- RESUMPTION PHASES --
--                   --

--
-- enclosing function for compilation of resumptions; this
-- appends "Done" to the end of the compiled resumption
--
-- (2010.10.02) Schulz
--
compile_R' :: INAST -> RC ([DDec], (Chain, [Code]))
compile_R' r = compile_R r >>= \(vs, (p, ps)) ->
               gendone >>= \d ->
               gendone >>= \d' ->
               let p' = Seq
                          (Throw d (FBy (Assign R_Req (DeRef done_sig)) End))
                          (Halt d')
               in
                 return (vs, (chaincat p p', ps))

compile_R :: INAST -> RC ([DDec], (Chain, [Code]))

--
-- VERY IMPORTANT: the lambda-bound variable must be assigned
-- as part of the atomic action on the LHS in order to ensure correctness;
-- each running resumption must behave as if it has its own copy of 'r_ret'
-- even though this is not actually the case.
--
-- If the assignment is not made, the resumption may be interrupted
-- and the value of r_ret overwritten.
--

compile_R (CTBindIN r (CTLamIN x r' t) _) =
                                  compile_R r >>= \(vs, (q, ps)) ->
                                  extenv x (VBind x) >>= \rho ->
                                  inEnv rho (compile_R r') >>= \(vs',(p',ps'))->
                                  let p  = retsave x q
                                      xd = VDec x (torsity (domof t))
                                  in
                                    return
                                      (xd:(vs ++ vs'),
                                         (chaincat p p', ps ++ ps'))


compile_R (CTBindIN r r'@(CTVarIN f _)  _) =
                                 compile_R r >>= \(vs, (q, ps)) ->
                                 genpause >>= \l ->
                                 genback >>= \l' ->
                                 argsof f >>= \[x] ->
                                  
                                 let p   = retsave x q
                                     f'  = funlabel f
                                     bk  = rtsreg f'
                                     f'' = LabelRef f'
                                     rts = Atom l
                                             (FBy
                                               (Assign (Var bk)
                                                 (DeRef (LabelRef l')))
                                                   End)
                                     jmp = Seq rts (Jmp l f'' (Halt l'))
                                 in
                                   return (vs, (chaincat p jmp, ps))

--
-- currently expecting no other cases for bind,
-- partial application is not allowed
--
-- (2010.09.20) Schulz
--


compile_R (CTNullBindIN r r' _) = compile_R r >>= \(vs, (p, ps)) ->
                                  compile_R r' >>= \(vs', (p', ps')) ->
                                  return (vs ++ vs', (chaincat p p', ps ++ ps'))

compile_R (CTReturnIN x _)      = compile_I x >>= \(vs, (e, ps)) ->
                                  genretlabel >>= \l ->
                                  genpause >>= \l' ->
                                  let (s', ps') = setup_x ps
                                  in
                                    let s  = FBy (Assign R_Ret e) End
                                        a  = Atom l (asmcat s' s)
                                        p  = Seq a (Halt l')
                                    in
                                      return (vs, (p, ps'))


--
--
-- the lambda-bound variable necessary for passing the value of 'r_ret'
-- to the next action must be assigned BEFORE the next pause, i.e.
-- before the end of the atom in the LHS of a bind.  Therefore, the compiler
-- needs to always view lambdas in the context of a bind, so as to correctly
-- situate the assignment.
--
--
-- (2010.09.20) Schulz
--
{-
compile_R (CTLamIN x r _)       = genlamlabel >>= \l ->
                                  let s = Block l
                                           (FBy (varassign x (DeRef R_Ret)) End)
                                  in
                                    extenv x (VBind x) >>= \rho' ->
                                    inEnv rho' (compile_R r) >>= \(p, ps) ->
                                    return (Seq s p, ps)
-}

--
-- deconstructing resumptions; see 'talk-2010.08.27.tex' for definition
-- and some details of the compilation and why it is this way
--
-- (2010.09.07) Schulz
--

compile_R (CTResumeIN r _) = compile_Re r >>= \(vs, (p, ps)) ->
                             genpause >>= \l ->
                             gendone >>= \l'' ->
                             genpause >>= \l''' ->
                             let l'  = startof p
                                 p'  = R l' p
                                 nxt = Atom l'''
                                         (FBy 
                                           (Assign R_Ret (DeRef R_Nxt))
                                             End)

                                 ret = Seq nxt (Halt l'')
                             in
                               return
                                 (vs, (Swr l (LabelRef l') ret, p':ps))


compile_R (CTResumeReIN r s _) = compile_Re r >>= \(vs, (p, ps)) ->
                                 compile_I s >>= \(vs', (q, qs)) ->
                                 genpause >>= \l ->
                                 gendone >>= \l'' ->
                                 genpause >>= \l''' ->
                                 genpause >>= \l'''' ->
                                 let (q', qs') = setup_x qs
                                 in
                                 let l'  = startof p
                                     p'  = R l' p

                                     rsp = Atom l''''
                                             (asmcat q'
                                               (FBy (Assign R_Ret q) End))

                                     nxt = Atom l'''
                                             (FBy 
                                               (Assign R_Ret (DeRef R_Nxt))
                                                 End)

                                     ret = Seq nxt (Halt l'')
                                 in
                                   return
                                     (vs ++ vs', 

                                       (Seq rsp
                                         (Swt l (LabelRef l') ret),
                                           p':(ps ++ qs')))


--
-- fetching the signal from a reactive resumption, which is a
-- a little funky:
--
-- run the first atom of the target, which, by convention, should
-- throw a signal; pass this back through 'r_ret';
--
-- (2010.09.23) Schulz
--
compile_R (CTGetReqIN r _) = compile_Re r >>= \(vs, (p, ps)) ->
                             genpause >>= \l' ->
                             genpause >>= \l'' ->
                             genpause >>= \l''' ->
                             gendone >>= \l'''' ->
                             let l   = LabelRef (startof p)

                                 -- must be 'swr', not 'swt' here;
                                 -- 'swr' will interrupt after signal throw.
                                 a   = Atom l'''
                                         (FBy (Assign R_Ret (DeRef R_Req)) End)
                                 r'  = Swr l' l (Halt l'')

                                 r'' = chaincat r' (Seq a (Halt l''''))
                             in
                               return (vs, (r'', (R (startof p) p):ps))

{-
compile_R (CTResumeReIN r s _) = compile_Re r >>= \(p, ps) ->
                                 compile_I s >>= \(q, qs) ->
                                 genpause >>= \l ->
                                 gendone >>= \l'' ->
                                 genpause >>= \l''' ->
                                 genpause >>= \l'''' ->
                                 let l'  = startof p
                                     p'  = R l' p
                                     rsp = Atom l''''
                                             (FBy
                                               (Assign R_Ret q)
                                                 End)
                                     nxt = Atom l'''
                                             (FBy 
                                               (Assign R_Ret (DeRef R_Nxt))
                                                 End)

                                     ret = Seq nxt (Halt l'')
                                 in
                                   return
                                     (Seq rsp
                                       (Swr l (LabelRef l') ret),
                                         p':(ps ++ qs))
-}



--
-- implicit in the special 'bind' case above,
-- this case should only be reached when 'step' is the
-- last item in a bind, or occurs by itself
--

compile_R (CTStepIN k _)        = compile_K k >>= \(vs, ((Block t p), ps)) ->
                                  genpause >>= \l ->
                                  gendone >>= \l' ->
                                  genpause >>= \at ->

                                  let p'   = Halt l'

                                      -- duplicate the label of next
                                      -- action in 'r_nxt'
                                      nxt  = Assign R_Nxt
                                               (DeRef (LabelRef l'))

                                      a    = Atom at (asmcat p (FBy nxt End))
                                  in
                                    return
                                      (vs, (Seq a p', ps))



compile_R (CTBranchIN g r r' _) = compile_I g >>= \(vs, (c, ps'')) ->
                                  compile_R r >>= \(vs', (p, ps)) ->
                                  compile_R r' >>= \(vs'', (p', ps')) ->
                                  genpause >>= \l ->
                                  genpause >>= \l' ->
                                  genblklabel >>= \l'' ->
                                  let (s, qs) = setup_x ps''
                                      init    = Atom l'' s
                                  in
                                  return
                                    (vs ++ vs' ++ vs'',

                                      (Seq init (BZ_R l c p p' (Halt l')),
                                        qs ++ ps ++ ps'))

compile_R (CTLoopIN (CTLamIN x r t) _) =
                                  genlooplabel >>= \l ->
                                  extenv lex_loop (LBind l) >>= \rho ->
                                  inEnv rho (extenv x (VBind x)) >>= \rho' ->
                                  inEnv rho' (compile_R r) >>= \(vs, (p, ps)) ->
                                  genpause >>= \l' ->
                                  let p' = retsave x p
                                      xd = VDec x (torsity (domof t))
                                  in
                                    return (xd:vs, (Loop l p' (Halt l'), ps))

compile_R (CTBreakIN v _)       = compile_I v >>= \(vs, (e, ps)) ->
                                  genblklabel >>= \l ->
                                  rdEnv >>= \rho ->
                                  let (LBind l) = rho lex_loop
                                      (s, qs)   = setup_x ps
                                      init      = Atom l s
                                  in
                                    return (vs, (Seq init (Break l e), qs))

compile_R (CTVarIN f _)         = rdEnv >>= \rho ->
                                  genpause >>= \l ->
                                  genpause >>= \l' ->
                                  case (rho f) of

                                    (VBind r)      -> return
                                                        ([], 
                                                          (Jmp l (Var r)
                                                            (Halt l'),
  
                                                            []
                                                          ))

                                    (FBind f [] _) -> return
                                                        ([], 
                                                          (Jmp l (LabelRef f)
                                                            (Halt l'),

                                                            []
                                                        ))


--
-- the case where 'loop' is initialized
-- with an explicit application:
--
compile_R (CTLoopAppIN r@(CTLoopIN (CTLamIN x _ t) _) [e] _) =
                                  compile_R r >>= \(vs, (p, ps)) ->
                                  compile_I e >>= \(vs', (v, ps')) ->
                                  genretlabel >>= \l ->
                                  let (s, qs) = setup_x ps'
                                      init    = Assign (Var x) v
                                      init'   = asmcat s (FBy init End)
                                  in
                                    return
                                      (vs ++ vs', 
                                        (Seq (Atom l init') p, ps ++ qs))


--
-- ordinary function application:
--
compile_R (CTAppIN f x y)       =

  rdEnv >>= \rho ->
  

  let ((CTVarIN f' _), as) = uncurryapp (CTAppIN f x y)
      (FBind f'' xs t)     = rho f'
      as'                  = zip xs as
  in
  (
    foldr
    (\(x, a) -> \m ->

      compile_any a >>= \(vs, (p, ps)) ->

      case p of

        (Res r) -> let s = FBy (varassign x (DeRef (LabelRef (startof r)))) End
                   in
                     m >>= \(vs', (c, cs)) ->
                     return
                       (vs ++ vs', (asmcat s c, (R (startof r) r):(cs ++ ps)))
                     
        (Sta k) -> let s = FBy (varassign x (DeRef (LabelRef (startof k)))) End
                   in
                     m >>= \(vs', (c, cs)) ->
                     return
                       (vs ++ vs', (asmcat s c, (K (startof k) k):(cs ++ ps)))

        (Idn e) -> let s = FBy (varassign x e) End
                   in
                     m >>= \(vs', (c, cs)) ->
                     return
                       (vs ++ vs', (asmcat s c, (cs ++ ps)))

    ) (return ([], (End, []))) as'

  ) >>= \(vs, (c, cs)) ->
                                    
  genpause >>= \l ->
  genpause >>= \l' ->
  genpause >>= \l'' ->
  let init = Atom l c
      call = Jmp l' (LabelRef f'') (Halt l'')
  in
    return (vs, (Seq init call, cs))


--
-- this is a weird case that may not stay here,
-- or, if it does, will be really noteworthy
--
-- mostly, we need to do this in order to compile
-- our favorite kernel example without the need to
-- make tail calls explicit
--
-- presently, this is treated as a special-case variable
--
-- (2010.09.08) Schulz
--
compile_R (CTPrim1aryIN (Un Fst) (CTVarIN r _) _) =

  rdEnv >>= \rho ->
  genpause >>= \l ->
  genpause >>= \l' ->
  case (rho r) of

    (VBind r)      -> return
                        ([], 
                          (Jmp l (StructFld (Var r) fst_field) (Halt l'),
                            []))
                          

compile_R (CTPrim1aryIN (Un Snd) (CTVarIN r _) _) =

  rdEnv >>= \rho ->
  genpause >>= \l ->
  genpause >>= \l' ->
  case (rho r) of

    (VBind r)      -> return
                        ([],
                          (Jmp l (StructFld (Var r) snd_field) (Halt l'),
                            []))


--
-- the reactive resumption phase;
--
-- almost identical to the cases for ordinary resumptions
--

--
-- enclosing function for appending the 'done' signal;
-- identical to case for R above;
--
--
-- (2010.10.02) Schulz
--
compile_Re' :: INAST -> RC ([DDec], (Chain, [Code]))
compile_Re' r = compile_Re r >>= \(vs, (p, ps)) ->
                gendone >>= \d ->
                gendone >>= \d' ->
                let p' = Seq
                           (Throw d (FBy (Assign R_Req (DeRef done_sig)) End))
                           (Halt d')
                in
                  return (vs, (chaincat p p', ps))


compile_Re :: INAST -> RC ([DDec], (Chain, [Code]))

compile_Re (CTBindIN (CTSignalIN q _) (CTLamIN x r' t) _) =

                                compile_I q >>= \(vs, (e, ps)) ->
                                extenv x (VBind x) >>= \rho ->
                                inEnv rho (compile_Re r') >>= \(vs',(p',ps')) ->
                                genpause >>= \l ->
                                genpause >>= \l' ->
                                genpause >>= \l'' ->
                                let (q', qs') = setup_x ps
                                    req       = Assign R_Req e
                                    nxt       = Assign R_Nxt
                                                  (DeRef (LabelRef l'))
                                    s         = FBy req (FBy nxt End)
                                    thr       = Throw l (asmcat q' s)
                                    cat       = Catch l' (Var x) p'
                                    xd        = VDec x (torsity (domof t))
                                in
                                  return
                                    (xd:(vs ++ vs'),
                                      (Seq thr cat, qs' ++ ps'))
                                    

compile_Re (CTBindIN r (CTLamIN x r' _) _) =
                                compile_Re r >>= \(vs, (q, ps)) ->
                                extenv x (VBind x) >>= \rho ->
                                inEnv rho (compile_Re r') >>= \(vs',(p',ps')) ->
                                let p = retsave x q
                                in
                                  return
                                    (vs ++ vs', 
                                      (chaincat p p', ps ++ ps'))

compile_Re (CTBindIN r r'@(CTVarIN f _)  _) =
                                  compile_Re r >>= \(vs, (q, ps)) ->
                                  genpause >>= \l ->
                                  genback >>= \l' ->
                                  argsof f >>= \[x] ->
                                  
                                  let p   = retsave x q
                                      f'  = funlabel f
                                      bk  = rtsreg f'
                                      f'' = LabelRef f'
                                      rts = Atom l
                                              (FBy
                                                (Assign (Var bk)
                                                  (DeRef (LabelRef l')))
                                                    End)
                                      jmp = Seq rts (Jmp l f'' (Halt l'))
                                  in
                                    return (vs, (chaincat p jmp, ps))



compile_Re (CTNullBindIN (CTSignalIN q _)  r' _) =
                                   compile_I q >>= \(vs, (x, qs)) ->
                                   compile_Re r' >>= \(vs', (p', ps')) ->
                                   genpause >>= \l ->
                                   genpause >>= \l' ->
                                   let (q', qs') = setup_x qs
                                       nxt       = Assign R_Nxt
                                                     (DeRef
                                                       (LabelRef (startof p')))
                                       req       = Assign R_Req x
                                       thr       = Throw l
                                                     (asmcat q'
                                                       (FBy nxt (FBy req End)))

                                       -- this will assign r_ret to itself,
                                       -- thus inducing no new assignment,
                                       -- in keeping with the null-bind def;
                                       cat       = Catch l' R_Ret p'
                                   in
                                     return
                                       (vs ++ vs',
                                         (Seq thr cat, qs' ++ ps'))

compile_Re (CTNullBindIN r r' _) = compile_Re r >>= \(vs, (p, ps)) ->
                                   compile_Re r' >>= \(vs', (p', ps')) ->
                                   return
                                     (vs ++ vs',
                                       (chaincat p p', ps ++ ps'))

compile_Re (CTReturnIN x _)      = compile_I x >>= \(vs, (e, ps)) ->
                                   genretlabel >>= \l ->
                                   genpause >>= \l' ->
                                   let (s', ps') = setup_x ps
                                   in
                                     let s  = FBy (Assign R_Ret e) End
                                         a  = Atom l (asmcat s' s)
                                         p  = Seq a (Halt l')
                                     in
                                       return (vs, (p, ps'))
                                    

--
-- the exception to the atomicity rule for lambda-bound variable
-- assignment is the case of 'CTSignal', i.e. 'throw', where the
-- value of 'r_ret' is expected to be written by the caller, and NOT
-- produced by the preceding action;
--
-- this is made explicit in the special case for 'bind' above;
--
-- (2010.09.23) Schulz
--
{-
compile_Re (CTLamIN x r _)       = genlamlabel >>= \l ->
                                   let s = Block l
                                           (FBy (varassign x (DeRef R_Ret)) End)
                                   in
                                     extenv x (VBind x) >>= \rho' ->
                                     inEnv rho' (compile_Re r) >>= \(p, ps) ->
                                     return (Seq s p, ps)
-}


--
-- in accordance with the semantic definition of 'step_Re',
-- reactive atomicity is two-stepped also;
-- compiler produces a 'throw' to clear the active request,
-- and an 'atom' containing the compiled argument
--
--

compile_Re (CTStepIN k _)       = compile_K k >>= \(vs, ((Block t p), ps)) ->
                                  genpause >>= \l ->
                                  gendone >>= \l' ->
                                  gendone >>= \l'' ->
                                  genpause >>= \at ->

                                  let p'   = Halt l''

                                      thr  = nothrow l'

                                      -- duplicate the label of next
                                      -- action in 'r_nxt'
                                      nxt  = Assign R_Nxt
                                               (DeRef (LabelRef l''))

                                      act  = asmcat p (FBy nxt End)

                                      a    = Atom at (asmcat p (FBy nxt End))
                                  in
                                    return
                                      (vs, (Seq thr (Seq a p'), ps))

compile_Re (CTSignalIN q _)     = compile_I q >>= \(vs, (q', qs)) ->
                                  genpause >>= \l ->
                                  genpause >>= \l' ->
                                  gendone >>= \l'' ->
                                  let (g, qs') = setup_x qs
                                      req      = Assign R_Req q'
                                      nxt      = Assign R_Nxt
                                                   (DeRef (LabelRef l''))
                                      sig      = Throw l (asmcat g
                                                   (FBy req (FBy nxt End)))
                                  in
                                    return (vs, (Seq sig (Halt l''), qs'))
                                    


compile_Re (CTBranchIN g r r' _) = compile_I g >>= \(vs, (c, ps'')) ->
                                   compile_Re r >>= \(vs', (p, ps)) ->
                                   compile_Re r' >>= \(vs'', (p', ps')) ->
                                   genpause >>= \l ->
                                   genpause >>= \l' ->
                                   genblklabel >>= \l'' ->
                                   genblklabel >>= \l''' ->
                                   let (s, qs) = setup_x ps''
                                       init    = Atom l'' s
                                   in
                                   return
                                     (vs ++ vs' ++ vs'', 

                                       (Seq (nothrow l''')
                                         (Seq init
                                           (BZ_R l c p p' (Halt l'))),
                                             qs ++ ps ++ ps'))


compile_Re (CTLoopIN (CTLamIN x r t) _) =
                                  genlooplabel >>= \l ->
                                  extenv lex_loop (LBind l) >>= \rho ->
                                  inEnv rho (extenv x (VBind x)) >>= \rho' ->
                                  inEnv rho' (compile_Re r) >>= \(vs,(p, ps)) ->
                                  genpause >>= \l' ->
                                  let p' = retsave x p
                                      xd = VDec x (torsity (domof t))
                                  in
                                    return (xd:vs, (Loop l p' (Halt l'), ps))

compile_Re (CTBreakIN v _)       = compile_I v >>= \(vs, (e, ps)) ->
                                   genblklabel >>= \l ->
                                   rdEnv >>= \rho ->
                                   let (LBind l) = rho lex_loop
                                       (s, qs)   = setup_x ps
                                       init      = Atom l s
                                   in
                                     return (vs, (Seq init (Break l e), qs))

compile_Re (CTVarIN f _)         = rdEnv >>= \rho ->
                                   genpause >>= \l ->
                                   genpause >>= \l' ->
                                   case (rho f) of

                                     (VBind r)      -> return
                                                         ([],
                                                           (Jmp l (Var r)
                                                             (Halt l'),

                                                             []
                                                           )
                                                         )

                                     (FBind f [] _) -> return
                                                         ([], 
                                                           (Jmp l (LabelRef f)
                                                             (Halt l'),

                                                             []
                                                           )
                                                         )

--
-- special case where 'loop' is initialized
-- with an explicit application:
--
-- note that the loop variable ('x' in the lambda)
-- must be assigned atomically before the loop begins;
-- using 'ret' instead may result in a conflict
--
compile_Re (CTLoopAppIN r@(CTLoopIN (CTLamIN x _ _) _) [e] _) =
                                   compile_Re r >>= \(vs, (p, ps)) ->
                                   compile_I e >>= \(vs', (v, ps')) ->
                                   genretlabel >>= \l ->
                                   genpause >>= \l' ->
                                   let (s, qs) = setup_x ps'
                                       init    = Assign (Var x) v
                                       init'   = asmcat s (FBy init End)
                                   in
                                     return
                                        (vs ++ vs', 

                                        (Seq (nothrow l')
                                          (Seq (Atom l init') p),
                                            ps ++ qs))


--
-- ordinary function application:
--
compile_Re (CTAppIN f x y)       =

  rdEnv >>= \rho ->
  

  let ((CTVarIN f' _), as) = uncurryapp (CTAppIN f x y)
      (FBind f'' xs t)     = rho f'
      as'                  = zip xs as
  in
  (
    foldr
    (\(x, a) -> \m ->

      compile_any a >>= \(vs, (p, ps)) ->

      case p of

        (Res r) -> let s = FBy (varassign x (DeRef (LabelRef (startof r)))) End
                   in
                     m >>= \(vs', (c, cs)) ->
                     return
                       (vs ++ vs', 
                         (asmcat s c, (R (startof r) r):(cs ++ ps)))
                     
        (Sta k) -> let s = FBy (varassign x (DeRef (LabelRef (startof k)))) End
                   in
                     m >>= \(vs', (c, cs)) ->
                     return
                       (vs ++ vs', 
                         (asmcat s c, (K (startof k) k):(cs ++ ps)))

        (Idn e) -> let s = FBy (varassign x e) End
                   in
                     m >>= \(vs', (c, cs)) ->
                     return
                       (vs ++ vs', 
                         (asmcat s c, (cs ++ ps)))

    ) (return ([], (End, []))) as'

  ) >>= \(vs, (c, cs)) ->
                                    
  genpause >>= \l ->
  genpause >>= \l' ->
  genpause >>= \l'' ->
  let init = Atom l c
      call = Jmp l' (LabelRef f'') (Halt l'')
  in
    return (vs, (Seq init call, cs))


--
-- this is a weird case that may not stay here,
-- or, if it does, will be really noteworthy
--
-- mostly, we need to do this in order to compile
-- our favorite kernel example without the need to
-- make tail calls explicit
--
-- presently, this is treated as a special-case variable
--
-- (2010.09.08) Schulz
--
compile_Re (CTPrim1aryIN (Un Fst) (CTVarIN r _) _) =

  rdEnv >>= \rho ->
  genpause >>= \l ->
  genpause >>= \l' ->
  case (rho r) of

    (VBind r)      -> return
                        ([], 
                          (Jmp l (StructFld (Var r) fst_field) (Halt l'),
                            []))
                          
  

compile_Re (CTPrim1aryIN (Un Snd) (CTVarIN r _) _) =

  rdEnv >>= \rho ->
  genpause >>= \l ->
  genpause >>= \l' ->
  case (rho r) of

    (VBind r)      -> return
                        ([], 
                          (Jmp l (StructFld (Var r) snd_field) (Halt l'),
                            []))



--              -- 
-- STATE PHASES --
--              --

compile_K :: INAST -> RC ([DDec], (Block, [Code]))
compile_K = \k ->
            genblklabel >>= \l ->
            compile_K' k >>= \(vs, (p, ps)) ->
            return (vs, (Block l p, ps))


compile_K' :: INAST -> RC ([DDec], (ASM, [Code]))

compile_K' (CTBindIN k k' _)     = compile_K' k >>= \(vs, (p, ps)) ->
                                   compile_K' k' >>= \(vs', (p', ps')) ->
                                   return (vs ++ vs', (asmcat p p', ps ++ ps'))

compile_K' (CTNullBindIN k k' _) = compile_K' k >>= \(vs, (p, ps)) ->
                                   compile_K' k' >>= \(vs', (p', ps')) ->
                                   return (vs ++ vs', (asmcat p p', ps ++ ps'))

compile_K' (CTLamIN x k t)       = let s  = varassign x (DeRef R_Ret)
                                       xd = VDec x (torsity (domof t))
                                   in
                                     extenv x (VBind x) >>= \rho ->
                                     inEnv rho (compile_K' k) >>= \(vs,(p,ps))->
                                     return (xd:vs, (FBy s p, ps))

compile_K' (CTGetIN x _)         = let k = FBy (refassign R_Ret (vexpr x)) End
                                   in
                                     return ([], (k, []))

--
-- for now, I am going to pretend that no compound data structures
-- are being stored in the global state; hence the thrown-away code
-- in the 'compile_I' pattern
--
-- (2010.09.08) Schulz
--
compile_K' (CTPutIN x e _)       = compile_I e >>= \(vs, (e', _)) ->
                                   let k  = varassign x e'
                                       k' = refassign R_Ret Clear
                                   in
                                     return (vs, (FBy k (FBy k' End), []))


compile_K' (CTVarIN f _)        = rdEnv >>= \rho ->
                                  genback >>= \l ->
                                  case (rho f) of

                                    (VBind v)      -> let k = JSR l (Var v) End
                                                          b = Var (rtsreg f)
                                                          t = Assign b
                                                                (DeRef
                                                                  (LabelRef l))
                                                      in
                                                        return ([],(FBy t k,[]))

                                    -- K-typed arguments are inlined:
                                    (ABind c)      -> compile_K' c


                                    -- nullary functions produce jumps:
                                    (FBind f [] _) -> let k = JSR l
                                                                (LabelRef f) End
                                                          b = Var (rtsreg f)
                                                          t = Assign b
                                                                (DeRef
                                                                  (LabelRef l))
                                                      in
                                                        return ([],(FBy t k,[]))
                                                        

compile_K' (CTReturnIN x _)     = compile_I x >>= \(vs, (e, ps)) ->
                                  genretlabel >>= \l ->
                                  genpause >>= \l' ->
                                  let (s', ps') = setup_x ps
                                  in
                                    let s  = FBy (Assign R_Ret e) End
                                    in
                                      return (vs, (asmcat s' s, ps'))


--
-- function application with inlining of arguments;
--
-- produces a jump to a block containing a copy of the function body,
-- with code from arguments occupying the places of the parameters
--
compile_K' (CTAppIN f x t)       =

  rdEnv >>= \rho ->

  let ((CTVarIN f' _), as) = uncurryapp (CTAppIN f x t)
      (FBind f'' xs c)     = rho f'
      as'                  = zip xs as
      rho'                 = foldl
                             (\rho' -> \(x, a) ->

                               (\y -> if (y == x) then (ABind a) else (rho' y))

                             ) rho as'
  in
    genback >>= \bk ->
    inEnv rho' (compile_K c) >>= \(vs, (b, ps)) ->
    let l = startof b
        r = Assign (Var (rtsreg l)) (DeRef (LabelRef bk))
        p = FBy r (JSR bk (LabelRef l) End)
    in
      return (vs, (p, (K l b):ps))


{-
--
-- function application resulting in a stateful type
-- (essentially identical to the case in 'compile_R'):
--

compile_K' (CTAppIN f x t)       =

  rdEnv >>= \rho ->
  genback >>= \bk ->

  let ((CTVarIN f' _), as) = uncurryapp (CTAppIN f x t)
      (FBind f'' xs c)     = rho f'
      as'                  = zip xs as
  in
  (
    foldr
    (\(x, a) -> \m ->

      compile_any a >>= \(p, ps) ->

      case p of

        (Res r) -> let s = FBy (varassign x (DeRef (LabelRef (startof r)))) End
                   in
                     m >>= \(c, cs) ->
                     return (asmcat s c, (R (startof r) r):(cs ++ ps))
                     
        (Sta k) -> let l  = startof k
                       s  = FBy (varassign x (DeRef (LabelRef l))) End
                   in
                     m >>= \(c, cs) ->
                     return (asmcat s c, (K l k):(cs ++ ps))

        (Idn e) -> let s = FBy (varassign x e) End
                   in
                     m >>= \(c, cs) ->
                     return (asmcat s c, cs ++ ps)

    ) (return (End, [])) as'

  ) >>= \(c, cs) ->
                                    
  let init = c
      call = JSR bk (LabelRef f'') End
  in
    return (asmcat init call, cs)
-}



compile_I :: INAST -> RC ([DDec], (Expr, [Code]))

compile_I (CTCaseIN o as t) =

  rdEnv >>= \rho ->
  genvar >>= \v ->
  genvar >>= \w ->
  compile_I o >>= \(vs, (w', ws')) ->

  -- put the value of of the matched expression in w
  let m  = Assign (Var w) w'
      dv = VDec w (torsity t)
      dw = VDec v (torsity (typeofinast o))
  in

  -- compile the body of each alternative:
  (
    foldr
    (\(p, a) -> \m ->

      let xs  = patvars p
      in
        extenv_many (zip xs (map VBind xs)) >>= \rho' ->
        inEnv rho' (compile_I a) >>= \(vs, c) ->
        m >>= \(vs', cs) ->
        return (vs ++ vs', (c:cs))
    )
      (return ([], [])) as

  ) >>= \(vs', ps) ->

  let bs  = map (\(p, _) -> mkmatchcond (Var w) p) as

      -- form the assignments corresponding to pat var bindings:
      ss  = map (\(p, _) -> mkpatassigns rho (Var w) p) as

      -- put the initial assignments together with alt statements:
      ts  = map (\(_, ps) -> setup_x ps) ps
      ss' = zipWith asmcat ss (map fst ts)

      -- append final assignments to the output variable for each alt:
      ks  = map (\x -> Assign (Var v) x) (map fst ps)
      ks' = zipWith asmcat ss' (map (\a -> FBy a End) ks)
  in
    foldbranch (zip bs ks') >>= \bz ->
    genblklabel >>= \l ->
    return
      (dv:dw:(vs ++ vs'), 
        (DeRef (Var v),
          (K l (Block l (FBy m bz))):(concat $ map snd ts)))


compile_I (CTPrim1aryIN (Un op) e _) =

  compile_I e >>= \(vs, (x, ps)) ->

  case op of
    CTNeg -> return ([], (Neg x, ps))
    CTNot -> return ([], (Not x, ps))

    _     -> case x of
               (DeRef (Var v)) -> case op of
                                    Fst -> return
                                             ([], 
                                               (DeRef
                                                 (StructFld (Var v) fst_field),
                                                   ps))

                                    Snd -> return
                                             ([], 
                                               (DeRef
                                                 (StructFld (Var v) snd_field),
                                                   ps))
             


compile_I (CTPrim2aryIN (Bin op) e e' _) =

  compile_I e >>= \(vs, (x, ps)) ->
  compile_I e' >>= \(vs', (x', ps')) ->

  case op of

    CTPlus      -> return ([], (Add x x', ps ++ ps'))
    CTMinus     -> return ([], (Sub x x', ps ++ ps'))
    CTMult      -> return ([], (Mul x x', ps ++ ps'))
    CTIDiv      -> return ([], (Div x x', ps ++ ps'))

    CTAnd       -> return ([], (And x x', ps ++ ps'))
    CTOr        -> return ([], (Or x x', ps ++ ps'))

    CTEqTest    -> return ([], (EqTest x x', ps ++ ps'))
    CTIneqTest  -> return ([], (IneqTest x x', ps ++ ps'))
    CTLTTest    -> return ([], (LTTest x x', ps ++ ps'))
    CTGTTest    -> return ([], (GTTest x x', ps ++ ps'))
    CTLTETest   -> return ([], (LTETest x x', ps ++ ps'))
    CTGTETest   -> return ([], (GTETest x x', ps ++ ps'))


compile_I (CTVarIN x _) = rdEnv >>= \rho ->
                          case (rho x) of
                            (VBind v) -> return ([], (DeRef (Var v), []))
                            (ABind v) -> compile_I v

--
-- treat an identity-typed function as a macro:
--
-- (2010.10.05) Schulz
--
compile_I (CTAppIN f x y) =

  let ((CTVarIN f' _), as) = uncurryapp (CTAppIN f x y)
  in
    termof f' >>= \t ->
    argsof f' >>= \xs ->
    extenv_many (zip xs (map ABind as)) >>= \rho ->
    inEnv rho (compile_I t)


compile_I (CTPairIN x y t) =

  compile_any x >>= \(vs, (p, ps)) ->
  compile_any y >>= \(vs', (p', ps')) ->
  genblklabel >>= \l ->
  genvar >>= \v ->
  let f  = StructFld (Var v) fst_field
      s  = StructFld (Var v) snd_field
      a  = FBy (Assign f (eval p))
             (FBy (Assign s (eval p')) End)
      b  = Block l a
      dv = VDec v (torsity t)
  in
    mkcode p >>= \q ->
    mkcode p' >>= \q' ->
    return (dv:(vs ++ vs'), (DeRef (Var v), (K l b):(q ++ q' ++ ps ++ ps')))



--
-- constructor application: implicitly create a struct,
-- and assign the fields in advance of using the variable;
-- this is coordinated by function 'setup_x', and the return
-- convention at the bottom of this case
--
-- (2010.09.23) Schulz
--
compile_I (CTConIN c as t) =

  rdEnv >>= \rho ->
  genvar >>= \v ->
  let (CBind c' rs) = rho c
      ss            = zip rs as
      mkc           = Assign
                        (StructFld (Var v) confld)
                        (DeRef (DecConstant c'))

      dv            = VDec v (torsity t)
  in

  (
    foldr
    (\(r, a) -> \m ->

      compile_any a >>= \(vs, (b, bs)) ->
      let fld = StructFld (Var v) r
          s   = Assign fld (eval b)
      in
        m >>= \(vs', (k, bs')) ->
        mkcode b >>= \b' ->
        return (vs ++ vs', (FBy s k, b' ++ bs ++ bs'))

    )
      (return ([], (FBy mkc End, []))) ss

  ) >>= \(vs, (st, bs)) -> 

  genblklabel >>= \l ->
  let b = Block l st
  in
    -- the convention of putting the initialization block at the top
    -- of the code-pile is important; it interfaces with setup_x
    --
    -- (2010.09.21) Schulz
    return (dv:vs, (DeRef (Var v), (K l b):bs))


compile_I (CTLitIN l _) =

  case l of
    (LitInt n)  -> return ([], (SInt n, []))
    (LitBool b) -> return ([], (SBool b, []))
    UnitEl      -> return ([], (Clear, []))


compile_I (CTUnitIN _) = return ([], (Clear, []))


--
-- transform an action into an expressible value:
--
eval :: Any -> Expr
eval (Res r) = DeRef (LabelRef (startof r))
eval (Sta s) = DeRef (LabelRef (startof s))
eval (Idn x) = x

--
-- package an action as a block of code:
--
mkcode :: Any -> RC [Code]
mkcode (Res r) = genblklabel >>= \l -> return [R l r]
mkcode (Sta k) = genblklabel >>= \l -> return [K l k]
mkcode (Idn _) = return []

--
-- unwrap and situate any code needed
-- for a (possible) structure generated by 'compile_I':
--
setup_x :: [Code] -> (ASM, [Code])
setup_x ((K _ (Block _ s)):ps) = (s, ps)
setup_x []                     = (End, [])



--                       --
-- INITIALIZATION PASSES --
--                       --

--
-- pass to make declarations for every state monad layer:
--
decglobals :: [MonadDec] -> [DDec]
decglobals =

  foldr
  (\m -> \d ->

    case m of
      (CTStateT _ ls)    -> foldr
                            (\l -> \d' ->

                              --
                              -- currenly use only base-typed global states;
                              -- the provisional (vestigial?) constructs
                              -- for arrays and stacks are what's being
                              -- passed over here;
                              -- 
                              -- (2010.10.12) Schulz
                              --
                              case l of
                                (StateL, (x, t)) -> (VDec x (torsity t)):d'

                                _                -> d'

                            ) d ls

      (CTResT _ _)       -> d

      (CTReactT _ _ _ _) -> d

  )
    []

--
-- pass to bind declared functions:
--
mkfenv :: [INFunDec] -> REnv
mkfenv =

  foldr
  (\(INFunDec ((f, t), (xs, p))) -> \rho ->

    let f' = funlabel f
        b  = FBind f' xs p
    in
      (\x -> if x /= f then rho x else b)

  )
    initenv


--
-- pass to bind data constructors:
--
mkconenv :: REnv -> [DataDec] -> REnv
mkconenv rho ds =

  let cons = foldr (\(DataDec _ _ ds) -> \ds' -> ds ++ ds') [] ds
  in

  foldr
  (\((TyCon c, ts)) -> \rho' ->

    let c' = mkcon c
        fs = mkflds c (map ppt ts)
        b  = CBind c' fs
    in
      (\x -> if x /= c then rho' x else b)

  ) (rho) cons



--                                               --
-- MINOR SYNTACTIC MANIPULATIONS AND BOILERPLATE --
--                                               --


--
-- get to-be-bound identifiers out of a pattern:
--
patvars :: CTPat -> [Reg]
patvars (PNest p _)     = patvars p
patvars (PTuple p p' _) = (patvars p) ++ (patvars p')
patvars (PCon _ ps _)   = concat $ map patvars ps
patvars (PPause p _)    = patvars p
patvars (PDone p _)     = patvars p
patvars (PPauseRe p _)  = patvars p
patvars (PDoneRe p _)   = patvars p
patvars (PCons p p' _)  = (patvars p) ++ (patvars p')
patvars (PList ps _)    = concat $ map patvars ps
patvars (PVar x _)      = [x]
patvars _               = []


--
-- generate a boolean expression from a pattern match:
--
mkmatchcond :: Ref -> CTPat -> Expr

mkmatchcond x (PNest p _) = mkmatchcond x p


--
-- deconstructors:
--
mkmatchcond x (PCon c ps _) =

  -- constructor match corresponds to equality with its declared constant:
  let cm = EqTest
             (DeRef (StructFld x confld))
             (DeRef (DecConstant (mkcon c)))

      -- associate each subpattern to its corresponding field
      fs = attachl structfld  ps

      -- form conditions for each of the subpatterns, localized
      -- to the proper field:
      fs' = map (\(m, p) -> mkmatchcond (StructFld x m) p) fs
  in
    foldr
      (\e -> \e' -> And e e') cm fs'

mkmatchcond _ (PVar _ _)   = SBool True
mkmatchcond _ (Wildcard _) = SBool True


mkpatassigns :: REnv -> Ref -> CTPat -> ASM
mkpatassigns rho x (PNest p _) = mkpatassigns rho x p

--
-- deconstructors:
--
mkpatassigns rho x (PCon c ps _) = let fs  = attachl structfld ps

                                       -- setup struct fields reffing the fields
                                       x'  = StructFld x insfld

                                       -- setup union actually containing fields
                                       x'' = StructFld x' $
                                               ((\(CBind c _) -> c)
                                                 (rho c))

                                       fs' = map
                                             (\(l, p) ->
                                               (StructFld x'' l, p))
                                                 fs
                                       as = map
                                              (\(v, p) -> mkpatassigns rho v p)
                                                fs'
                                   in
                                     foldr (\k -> \m -> asmcat k m) End as


mkpatassigns rho x (PVar v _)   = FBy (Assign (Var v) (DeRef x)) End
mkpatassigns rho x (Wildcard _) = End


foldbranch :: [(Expr, ASM)] -> RC ASM
foldbranch =

  foldr
    (\(x, p) -> \m ->

      genblklabel >>= \l ->
      genblklabel >>= \l' ->
      genblklabel >>= \l'' ->
      m >>= \b ->
      return (BZ_K x (Block l p) (Block l' b) (Block l'' End))

    )
      (return End)




chaincat :: Chain -> Chain -> Chain
chaincat (Seq x r) r'        = Seq x (chaincat r r')
chaincat (BZ_R l x t f r) r' = BZ_R l x t f (chaincat r r')
chaincat (Loop l r r') r''   = Loop l r (chaincat r' r'')
chaincat (Swr l v r) r'      = Swr l v (chaincat r r')
chaincat (Swt l v r) r'      = Swt l v (chaincat r r')
chaincat (Catch l v r) r'    = Catch l v (chaincat r r')
chaincat (Jmp l v r) r'      = Jmp l v (chaincat r r')
chaincat (Halt l) r'         = LabelPt l r'
chaincat (LabelPt l r) r'    = LabelPt l (chaincat r r')
-- take note of the omission: 'break' should never be concatenated!
-- (2010.08.19) Schulz



retsave :: Reg -> Chain -> Chain
retsave x (Seq a@(Atom l k) c) = if (noatoms c)
                                 then
                                   let a' = asmcat k
                                              (FBy
                                                (Assign (Var x) (DeRef R_Ret))
                                                  End)
                                   in
                                     Seq (Atom l a') c
                                 else
                                   Seq a (retsave x c)

--
-- note that 'throw' induces no retsave; the next retval is
-- expected to be written in by the caller; the mechanics of this
-- are handled by special cases in 'compile_R' and 'compile_Re';
--
-- (2010.09.24) Schulz
--
retsave _ (Seq a@(Throw _ _) c) = Seq a c

retsave x (BZ_R l g c c' c'')  = if (noatoms c'')
                                 then
                                   let a  = retsave x c
                                       a' = retsave x c'
                                   in
                                     BZ_R l g a a' c''
                                 else
                                   BZ_R l g c c' (retsave x c'')

retsave x (Loop l c c')        = if (noatoms c')
                                 then
                                   Loop l (retsave x c) c'
                                 else
                                   Loop l c (retsave x c')

retsave x (Swr l f c)          = Swr l f (retsave x c)

retsave x (Swt l f c)          = Swt l f (retsave x c)

retsave x (Catch l r c)        = Catch l r (retsave x c)

retsave x (Jmp l f c)          = Swr l f (retsave x c)

retsave x (LabelPt l c)        = LabelPt l (retsave x c)

retsave _ (Halt l)             = Halt l


noatoms :: Chain -> Bool
noatoms (BZ_R _ _ c c' c'') = (noatoms c) && (noatoms c') && (noatoms c'')
noatoms (Loop _ c c')       = (noatoms c) && (noatoms c')
noatoms (Jmp _ _ c)         = noatoms c
noatoms (LabelPt _ c)       = noatoms c
noatoms (Seq _ _)           = False
noatoms (Swr _ _ _)         = False
noatoms (Swt _ _ _)         = False
noatoms (Catch _ _ c)       = noatoms c
noatoms (Break _ _)         = False
noatoms (Halt _)            = True

spillvar :: Reg -> Reg -> Stmt
spillvar x y = Assign (Var x) ((DeRef (Var y)))

refassign :: Ref -> Expr -> Stmt
refassign r x = Assign r x

varassign :: Reg -> Expr -> Stmt
varassign x e = Assign (Var x) e

vexpr :: Reg -> Expr
vexpr x = DeRef (Var x)


uncurryapp :: INAST -> (INAST, [INAST])

uncurryapp (CTAppIN f x _) = let (f', xs) = uncurryapp f
                             in
                               (f', xs ++ [x])

uncurryapp (CTVarIN f t) = (CTVarIN f t, [])



domof :: CTTy -> CTTy
domof (CTAbsTy t _) = t

codomof :: CTTy -> CTTy
codomof (CTAbsTy _ t) = codomof t
codomof t             = t

argtsof :: CTTy -> [CTTy]
argtsof (CTAbsTy a b) = a:(argtsof b)
argtsof t             = []


attachl :: String -> [a] -> [(String, a)]
attachl s xs = zip (map (\x -> s ++ (show x)) ints ) xs

ints :: [Int]
ints = iterate (+ 1) 0


--           --
-- CONSTANTS --
--           --

program_entry = "main0"

funlabel f = '_':'_':f

mkcon c = '_':'_':(map toUpper c)

confld = "con"
insfld = "inst"

mkflds c fs = let cs  = zip (repeat c)
                          (zipWith (\s -> \n -> s ++ (show n)) fs ints)
              in
                map (\(c, f) -> c ++ '_':'_':f) cs

done_sig = SysConstant "__RDONE__"

pause_header_size = SysConstant "PAUSE_HEADER_SIZE"

fst_field = "fst"
snd_field = "snd"

structfld = "__field__"

nothrow l = Throw l (FBy (Clr R_Req) End)

--
-- This is a special symbol used in the environment
-- to keep track of lexical scoping of loops, for the purpose
-- of generating loop-exit labels:
--
-- This string should never appear in the output!
--
lex_loop :: String
lex_loop = "_____lexically_enclosing_loop_"


--
-- prefixes used in generated fresh variables:
--
resume_var :: String
resume_var = "__resume__"

internal_var :: String
internal_var = "__vvar__"

block_label :: String
block_label = "__BLOCK__"

res_var :: String
res_var = "__res_var__"

pause_label :: String
pause_label = "__PAUSE__"

done_label :: String
done_label = "__DONE__"

loop_label :: String
loop_label = "__LOOP__"

lam_label :: String
lam_label = "__LAM_BIND__"

ret_label :: String
ret_label = "__RETVAL__"

jumpback_label :: String
jumpback_label = "__JUMPBACK__"

initenv :: REnv
initenv = \_ -> NOBIND

initct :: Counter
initct = (0, 0, 0, 0, 0, 0, 0, 0, 0, 0)

-- THIS IS THE END OF THE FILE --
