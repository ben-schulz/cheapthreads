(*

 this is ~/cheapthreads/CTC/CT-1.0/RPSLam/Mechanization/STLC.v

 an attempt to contstruct a monadic interpreter semantics for a simply-typed
 lambda calculus in a simple setting, with the goal of applying this structure
 to the more complicated syntax in SLam

 put here 2011.05.19

 Schulz

*)

Require Import List.

Set Implicit Arguments.

Import Id.

Notation "## v" := (eta_id _ v).
Notation "x >>= f" := (bind_id _ _ x f).


Inductive type : Set :=
 | Unit : type
 | Nat : type
 | Arrow : type -> type -> type
 | Sum : type -> type -> type
 | Prod : type -> type -> type.

Fixpoint type_denote (t : type) : Set :=
 match t with
  | Unit => unit
  | Nat => nat
  | Arrow t' t'' => (type_denote t') -> (type_denote t'')
  | Sum t t' => ((type_denote t) + (type_denote t'))%type
  | Prod t t' => ((type_denote t) * (type_denote t'))%type
 end.

Section hlist.

Variable A : Type.
Variable B : A -> Type.

Inductive hlist : list A -> Type :=
 | HNil : hlist nil
 | HCons : forall (x : A) (ls : list A),
           B x -> hlist ls -> hlist (x :: ls).


Variable elm : A.

Inductive elem : list A -> Type :=
 | EHead : forall (ls : list A), elem (elm :: ls)
 | ENxt : forall (y : A) (ls : list A), elem ls -> elem (y :: ls).


Fixpoint hget ls (mls : hlist ls) : elem ls -> B elm :=
 match mls with
  | HNil =>
    fun mem =>
     match mem in elem ls' return (match ls' with
                                    | nil => B elm
                                    | _ :: _ => unit
                                   end) with
      | EHead _ => tt
      | ENxt _ _ _ => tt
     end

  | HCons _ _ x mls' =>
    fun mem => 
    match mem in elem ls' return (match ls' with
                                   | nil => Empty_set
                                   | x' :: ls'' =>
                                     B x' -> (elem ls'' -> B elm) -> B elm
                                  end) with
     | EHead _ => fun x _ => x
     | ENxt _ _ mem' => fun _ get_mls' => get_mls' mem'
    end x (hget mls')
  end.

End hlist.


Inductive exp : list type -> type -> Set :=
 | TT : forall (ts : list type), exp ts Unit
 | Const : forall (ts : list type), nat -> exp ts Nat
 | Var : forall (t : type) (ts : list type), elem t ts -> exp ts t

 | Abs : forall (ts : list type) (a b : type),
    exp (a :: ts) b -> exp ts (Arrow a b)
 | App : forall (ts : list type) (a b : type),
    exp ts (Arrow a b) -> exp ts a -> exp ts b

 | Case : forall (ts : list type) (t t' b : type),
    exp ts (Sum t t') ->
    exp (t :: ts) b ->
    exp (t' :: ts) b -> exp ts b

 | InL : forall (ts : list type) (t t' : type),
    exp ts t -> exp ts (Sum t t')
 | InR : forall (ts : list type) (t t' : type),
    exp ts t' -> exp ts (Sum t t')

 | Prj1 : forall (ts : list type) (t t' : type),
    exp ts (Prod t t') -> exp ts t
 | Prj2 : forall (ts : list type) (t t' : type),
    exp ts (Prod t t') -> exp ts t'
 | Cross : forall (ts : list type) (t t' : type),
    exp ts t -> exp ts t' -> exp ts (Prod t t').


Fixpoint exp_denote (ts : list type) (t : type) (e : exp ts t) :
 hlist type_denote ts -> type_denote t :=

 match e in (exp ts t) return (hlist type_denote ts -> type_denote t) with
  | TT _ => fun _ => tt
  | Const _ n => fun _ => n
  | Var _ _ mem => fun s => hget s mem

  | App _ _ _ e1 e2 => fun s => (exp_denote e1 s) (exp_denote e2 s)
  | Abs _ _ _ e' => fun s => fun x => exp_denote e' (HCons _ x s)

  | Case _ _ _ _ e' l r =>
     fun s =>
     match (exp_denote e' s) with
      | inl x => exp_denote l (HCons _ x s)
      | inr x => exp_denote r (HCons _ x s)
     end

  | InL _ _ _ e' => fun s => inl _ (exp_denote e' s)
  | InR _ _ _ e' => fun s => inr _ (exp_denote e' s)

  | Prj1 _ _ _ e' => fun s => fst (exp_denote e' s)
  | Prj2 _ _ _ e' => fun s => snd (exp_denote e' s)
  | Cross _ _ _ e' e'' => fun s => (exp_denote e' s, exp_denote e'' s)

 end.

Fixpoint exp_denotem (ts : list type) (t : type) (e : exp ts t) :
 hlist type_denote ts -> Id (type_denote t) :=

 match e in (exp ts t) return (Id (hlist type_denote ts -> type_denote t)) with
  | TT _ => fun _ => ## tt
  | Const _ n => fun _ => ## n
  | Var _ _ mem => fun s => ## (hget s mem)

  | App _ _ _ e1 e2 => fun s =>
                       exp_denote e1 s >>= fun f =>
                       f (exp_denote e2 s)

  | Abs _ _ _ e' => fun s =>
                    ## (fun x => exp_denote e' (HCons _ x s))

  | InL _ _ _ e' => fun s => ## (inl _ (exp_denote e' s))
  | InR _ _ _ e' => fun s => ## (inr _ (exp_denote e' s))
  | Case _ _ _ _ e' l r =>
     fun s =>
     match (exp_denote e' s) with
      | inl x => exp_denote l (HCons _ x s)
      | inr x => exp_denote r (HCons _ x s)
     end

  | Prj1 _ _ _ e' =>
     fun s =>
     exp_denote e' s >>= fun v => ## (fst v)

  | Prj2 _ _ _ e' =>
     fun s =>
     exp_denote e' s >>= fun v => ## (snd v)

  | Cross _ _ _ e' e'' =>
     fun s =>
     exp_denote e' s >>= fun v =>
     exp_denote e'' s >>= fun v' =>
     ## (v, v')
 end.
