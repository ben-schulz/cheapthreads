--
-- this is ~/cheapthreads/ctc_working/CT-1.0/RPSLam/Compile/Codegen.hs
--
-- generation of a simplified target language from the RPS terms produced
-- by the interpreter phase ('Compile.RPSInterp.hs')
--
-- put here (2010.12.15)
--
-- Schulz
--

module Compile.CodeGen where

import Compile.ReSyntax
import Compile.Constants
import Targets.Syntax

import MonadicConstructions

type M a = StateT (Int, Int, Int) Id a

genlocal :: M Label
genlocal = get >>= \(n, _, _) ->
           upd (\(n, m, o) -> (n + 1, m, o)) >>
           return (tlocal ++ (show n))

genbind :: M Label
genbind = get >>= \(_, m, _) ->
          upd (\(n, m, o) -> (n, m + 1, o)) >>
          return ("BIND" ++ (show m))

genbrs :: M (Label, Label)
genbrs = get >>= \(_, _, o) ->
         upd (\(n, m, o) -> (n, m, o + 1)) >>
         let n' = show o
         in
           return ("BRTRUE" ++ n', "BRFALSE" ++ n')

codegen :: TermRe -> Prog
codegen t = (Prog .
              (\((Act l x), y) -> (Act mainl (Labeled l x)):y) . fst . deId)
                ((deST (compile_act t)) (0, 0, 0))



--
-- compile and wrap term as a stand-alone action
-- that will throw back to the handler upon completion:
--
compile_act :: TermRe -> M (Act, [Act])
compile_act t = compile_term t >>= \(p, bs) ->
                genlocal >>= \l -> 
                genlocal >>= \l' -> 
                let dn = Assign R_Done (VX (BolT True))
                    ex = Labeled l' (Seq dn (Seq Return End))
                in
                  return (Act l (codecat p ex), bs)


--
-- fst: the sequential flow of the compiled expression;
-- snd: every other block that must be produced for this expression,
--      (namely, those needed for closures)
--
compile_term :: TermRe -> M (Code, [Act])

compile_term (Bind x t@(Signal _) t') = genlocal >>= \l ->
                                        genlocal >>= \l' ->
                                        compile_term t >>= \(p, bs) ->
                                        compile_term t' >>= \(p', bs') ->

                                        let bn  = Assign (Var x) (DeRef R_Ret)

                                            b   = Labeled l p
                                            b'  = Labeled l' (Seq bn p')
                                        in
                                          return (codecat b b', bs ++ bs')


compile_term (Bind x t t')     = genlocal >>= \l ->
                                 genlocal >>= \l' -> 
                                 compile_term t >>= \(p, bs) ->
                                 compile_term t' >>= \(p', bs') ->
                                 let bn = Assign (Var x) (DeRef R_Ret)
                                     b  = Labeled l p
                                     b' = Labeled l' (Seq bn p')
                                 in
                                   return
                                     (codecat b b', bs ++ bs')

compile_term (BindNull t t')   = genlocal >>= \l ->
                                 genlocal >>= \l' -> 
                                 compile_term t >>= \(p, bs) ->
                                 compile_term t' >>= \(p', bs') ->
                                 let b  = Labeled l p
                                     b' = Labeled l' p'
                                 in
                                   return
                                     (codecat b b', bs ++ bs')
                                

compile_term (Signal q)       = genlocal >>= \l ->
                                genlocal >>= \l' ->
                                compile_req q >>= \(q', ps) ->
                                let rq  = Assign R_Req q'
                                    rp  = Assign R_Ret (DeRef R_Rsp)
                                    dn  = Assign R_Done (VX (BolT False))
                                    nx  = Assign R_Nxt (VX (LabelT l'))

                                    rq' = Labeled l
                                            (Seq nx (Seq rq (Seq dn End)))
                                    rp' = Labeled l' (Seq rp End)
                                    rt  = Assign R_Ret (DeRef R_Rsp)
                                in
                                  return (codecat rq' (Seq Return rp'), ps)
                                    
                                  

compile_term (ITE x t t')     = compile_expr x >>= \(x', bs) -> 
                                compile_term t >>= \(p, bs') ->
                                compile_term t' >>= \(p', bs'') ->
                                genbrs >>= \(l, l') ->
                                genlocal >>= \l'' ->
                                genlocal >>= \l''' ->
                                let tr = codecat
                                           (Labeled l p) (Seq (JmpI l'') End)

                                    fl = Labeled l' p'
                                    cn = Labeled l'' (Seq Nop End)

                                    bz  = BZ x' l'
                                in
                                  return
                                    (Labeled l'''
                                      (Seq bz (codecat tr (codecat fl cn))),
                                        bs ++ bs' ++ bs'')
                                      

compile_term (Eta x)          = compile_expr x >>= \(x', bs) ->
                                genlocal >>= \l ->
                                return
                                  (Labeled l (Seq (Assign R_Ret x') End), bs)



compile_expr :: RExpr -> M (TExpr, [Act])

compile_expr (IncX v)            = compile_expr v >>= \(x, ps) -> 
                                   return (Inc x, ps)

compile_expr (DecX v)            = compile_expr v >>= \(x, ps) -> 
                                   return (Dec x, ps)

compile_expr (EqTest v v')       = compile_expr v >>= \(x, ps) ->
                                   compile_expr v' >>= \(x', ps') ->
                                   return
                                     (EqTst x x', (ps ++ ps'))

compile_expr (IsNum v)           = compile_expr v >>= \(x, ps) ->
                                   return (IsNumT x, ps)

compile_expr (IsBool v)          = compile_expr v >>= \(x, ps) ->
                                   return (IsBoolT x, ps)

compile_expr (IsCl v)            = compile_expr v >>= \(x, ps) ->
                                   return (IsClT x, ps)

compile_expr (IsRecCl v)         = compile_expr v >>= \(x, ps) ->
                                   return (IsRecClT x, ps)

compile_expr (Ref x)             = return (DeRef (Var x), [])

compile_expr (Lit (Cl x e r))    = compile_act r >>= \(p, bs) ->
                                   return
                                     (VX (ClT x e (RER (labelof p))), p:bs)

compile_expr (Lit (RecCl x e r)) = compile_act r >>= \(p, bs) ->
                                   return
                                     (VX (RecClT x e (RER (labelof p))), p:bs)

compile_expr (Lit v)             = return (VX (compile_val v), [])



compile_val :: RVal -> TVal
compile_val Wrong         = WrongT
compile_val (Num n)       = NumT n
compile_val (Bol b)       = BolT b



compile_req :: Req -> M (TExpr, [Act])
compile_req (MkCl x t)    = compile_act t >>= \(r, rs) ->
                            let l   = labelof r
                                con = (confld, (VX (SymConstant qmkcl)))
                                fs  = attachl structfld
                                        [VX (NameT x), VX (LabelT l)]
                            in
                              return (ConX qmkcl (con:fs), r:rs)

compile_req (MkRecCl x t) = compile_act t >>= \(r, rs) ->
                            let l   = labelof r
                                con = (confld, (VX (SymConstant qmkreccl)))
                                fs  = attachl structfld
                                        [VX (NameT x), VX (LabelT l)]
                            in
                              return (ConX qmkreccl (con:fs), r:rs)

compile_req (Apply v v')  = compile_expr v >>= \(x, ps) -> 
                            compile_expr v' >>= \(x', ps') -> 
                            let con = (confld, (VX (SymConstant qapply)))
                                fs  = attachl structfld [x, x']
                            in
                            return (ConX qapply (con:fs), ps ++ ps')

compile_req (Lkp x)       = let con = (confld, (VX (SymConstant qlkp)))
                                fs  = attachl structfld [VX (NameT x)]
                            in
                              return (ConX qlkp (con:fs), [])

{-
compile_req (MkCl x t)    = compile_act t >>= \(r, rs) ->
                            let l = labelof r
                            in
                              return (TMkCl x (RER l), r:rs)

compile_req (MkRecCl x t) = compile_act t >>= \(r, rs) ->
                            let l = labelof r
                            in
                              return (TMkRecCl x (RER l), r:rs)

compile_req (Apply v v')  = compile_expr v >>= \(x, ps) -> 
                            compile_expr v' >>= \(x', ps') -> 
                            return (TApply x x', ps ++ ps')

compile_req (Lkp x)       = return (TLkp x, [])
-}



--
-- get the first assignment to 'r_req'
-- (for use in making initialization code)
--
init_req :: Code -> TExpr
init_req (Labeled _ p)            = init_req p
init_req (Seq (Assign R_Req x) _) = x
init_req (Seq _ p)                = init_req p


--
-- get the first assignment to 'r_nxt'
-- (for use in making initialization code)
--
init_nxt :: Code -> TExpr
init_nxt (Labeled _ p)            = init_nxt p
init_nxt (Seq (Assign R_Nxt x) _) = x
init_nxt (Seq _ p)                = init_nxt p



--
-- make initialization code to run at the beginning of main;
--
-- an initial resumption ('initv') needs to be pushed onto the val stack
-- to be popped by the first round of the handler
--
--mkinit :: Code -> Code
--mkinit p =
mkinit :: Code
mkinit =

{-
  let v   = Var "initv"
      nx  = Assign (StructFld v callfld) (init_nxt p)
      rq  = Assign (StructFld v reqfld) (init_req p)
      dn  = Assign (StructFld v donefld) (VX (BolT False))
      dn' = Assign R_Done (VX (BolT False))
      fr  = Push (DeRef v)
-}

  let nx = Assign R_Nxt (VX WrongT)
      rq = Assign R_Req (VX WrongT)
      dn = Assign R_Done (VX WrongT)
      nv = Assign R_Env TopEnv
      rt = Assign R_Ret (VX WrongT)
  in
    Seq rt (Seq nv (Seq nx (Seq rq (Seq dn End))))
--    Seq rt (Seq nv (Seq nx (Seq rq (Seq dn (Seq dn' (Seq fr End))))))



-- THIS IS THE END OF THE FILE --
