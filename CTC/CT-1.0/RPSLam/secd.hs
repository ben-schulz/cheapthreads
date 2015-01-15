
module SECD where

import MonadicConstructions

type Var = Int
type Loc = Int

data Val = Unit | In1 Val | In2 Val | Pair Val Val | CL Var E Term | Loc Int

data Term = Const Val | Var Var
          | Inj1 Term | Inj2 Term
          | Prod Term Term
          | Lam Var Term          
          | Ref Term
          | Case Term Term Term
          | Prj1 Term | Prj2 Term
          | App Term Term
          | Mu Var Term
          | Deref Term          
          | Assign Term Term

data C' = AP | PRJ1 | PRJ2 | MATCH | DEREF | ASGN
        | PAIR | IN1 | IN2 | NEW | TERM Term
        | RETURN

type S = [Val]
type E = [(Var, Val)]
type C = [C']
type D = (S, E, C)

data Req = PUSH_S Val | PUSH_C C' | PUSH_D
         | POP_S | POP_C | RESTORE_D
         | EXT Var Val | MKCL Var Term | SETENV E
         | CLEAR_S | CLEAR_C
         | ALLOC | READ Loc | WRITE Loc Val
         | EMPTY_C | EMPTY_D | LKP Var
         | FRESH
                               
data Rsp = VAL Val | CMD C' | DMP D | BOOL Bool | VAR Var

type Re a = ReactT Req Rsp Id a

signal :: Req -> Re Rsp
signal q = P (q, \r -> return (return r))

loop :: (Re Bool) -> Re () -> Re ()
loop g x = g >>= \b -> if b then x >>= \v' -> loop g x else return ()

isdone :: Re Bool
isdone =
  signal EMPTY_C >>= \(BOOL b) ->
  signal EMPTY_D >>= \(BOOL b') ->
  return (b && b')


step :: Re ()
step =
  
  signal POP_C >>= \(CMD c) ->
  
  (
  case c of
    (TERM (Var x)) -> signal (LKP x) >>= \(VAL v) ->
                      signal (PUSH_S v)

    (TERM (App t t')) -> signal (PUSH_C AP) >>
                         signal (PUSH_C (TERM t)) >>
                         signal (PUSH_C (TERM t'))
                        
    AP -> signal POP_S >>= \(VAL (CL x e t)) ->
          signal POP_S >>= \(VAL v) ->
          signal PUSH_D >>
          signal (EXT x v) >>
          signal CLEAR_S >>
          signal CLEAR_C >>
          signal (PUSH_C (TERM t))
          
    RETURN -> signal POP_S >>= \(VAL v) ->
              signal RESTORE_D >>
              signal (PUSH_S v)
              
    (TERM (Lam x t)) -> signal (MKCL x t) >>= \(VAL (CL x e t)) ->
                        signal (PUSH_S (CL x e t))
                        
    (TERM (Mu f t)) -> signal FRESH >>= \(VAR x) ->
                       signal (MKCL f t) >>= \(VAL (CL _ e t)) ->
                       signal (EXT f (CL x e (App (Mu f t) (Var x)))) >>
                       signal PUSH_D >>
                       signal CLEAR_S >> signal CLEAR_C >>
                       signal (PUSH_C (TERM t))
    
    (TERM (Inj1 t)) -> signal (PUSH_C IN1) >>
                       signal (PUSH_C (TERM t))
    (TERM (Inj2 t)) -> signal (PUSH_C IN2) >>
                       signal (PUSH_C (TERM t))
                       
    IN1 -> signal POP_S >>= \(VAL v) ->
           signal (PUSH_S (In1 v))
    IN2 -> signal POP_S >>= \(VAL v) ->
           signal (PUSH_S (In2 v))
           
    TERM (Case t t' t'') -> signal FRESH >>= \(VAR x) ->
                            signal (PUSH_C MATCH) >>
                            signal (PUSH_C (TERM t)) >>
                            signal (MKCL x t') >>= \(VAL v) ->
                            signal (MKCL x t'') >>= \(VAL v') ->
                            signal (PUSH_S v') >>
                            signal (PUSH_S v)
                            
                       
    (TERM (Prod t t')) -> signal (PUSH_C PAIR) >>
                          signal (PUSH_C (TERM t')) >>
                          signal (PUSH_C (TERM t))

    PAIR -> signal POP_S >>= \(VAL v') ->
            signal POP_S >>= \(VAL v) ->
            signal (PUSH_S (Pair v v'))

    (TERM (Prj1 t)) -> signal (PUSH_C PRJ1) >>
                       signal (PUSH_C (TERM t))
    (TERM (Prj2 t)) -> signal (PUSH_C PRJ2) >>
                       signal (PUSH_C (TERM t))

    PRJ1 -> signal POP_S >>= \(VAL (Pair v _)) ->
            signal (PUSH_S v)
    PRJ2 -> signal POP_S >>= \(VAL (Pair _ v')) ->
            signal (PUSH_S v')

    (TERM (Ref t)) -> signal (PUSH_C NEW) >>
                      signal (PUSH_C (TERM t))

    (TERM (Assign t t')) -> signal (PUSH_C ASGN) >>
                            signal (PUSH_C (TERM t')) >>
                            signal (PUSH_C (TERM t))

    ASGN -> signal POP_S >>= \(VAL (Loc l)) ->
            signal POP_S >>= \(VAL v) ->
            signal (WRITE l v)

    (TERM (Deref t)) -> signal (PUSH_C DEREF) >>
                        signal (PUSH_C (TERM t))

    DEREF -> signal POP_S >>= \(VAL (Loc l)) ->
             signal (READ l) >>= \(VAL v) ->
             signal (PUSH_S v)

   ) >> return ()


secd :: Re ()
secd = loop isdone step