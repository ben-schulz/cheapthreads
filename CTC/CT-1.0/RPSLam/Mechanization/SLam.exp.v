(*
  this is ~/cheapthreads/CTC/CT-1.0/RPSLam/Mechanization/PHOAS.v

  a transition of the initial SLam mechanization into a style
  that exploits the verification advantages of Chlipala's PHOAS;


  yet another branch, to try to resolve the variable binder problem.

  it makes me envy the dead.


  put here 2011.05.02

  Schulz
*)

Require Import Arith.
Require Import Bool.

Import StateT.

Notation "## v" := (eta_sep _ _ v) (no associativity, at level 10).
Notation "x >>= f" := (bind_sep _ _ _ _ x f) (no associativity, at level 20).

Inductive stype : Set :=
 | H : stype
 | L : stype.

Definition stype_eqb (s s' : stype) : bool :=
 match s, s' with
  | H, H => true
  | L, L => true
  | _, _ => false
 end.

Theorem stype_eqb_eq :
 forall (s s' : stype), Is_true (stype_eqb s s') -> s = s'.

 unfold Is_true.
 destruct s; destruct s'; intuition; compute in H0; intuition.
Qed.


Inductive slower : stype -> stype -> Prop :=
 | HH : slower H H
 | LL : slower L L
 | LH : slower L H.

Notation "s |< s'" := (slower s s') (no associativity, at level 50).

Definition lub (s1 s2 : stype) : stype :=
 match (s1, s2) with
  | (H, _) => H
  | (_, H) => H
  | _ => L
 end.

Notation "s |_| s'" := (lub s s') (no associativity, at level 50).

Theorem lub_mon : forall (s s' : stype), s |< (s |_| s').

 destruct s; destruct s'; simpl lub; constructor.
Qed.

Theorem lub_comm : forall (s s' : stype), (s |_| s') = (s' |_| s).

 destruct s; destruct s'; simpl lub; constructor.
Qed.

Definition rtype : Set := (stype * stype)%type.

Definition rtype_eqb (r r' : rtype) : bool :=
 andb (stype_eqb (fst r) (fst r')) (stype_eqb (snd r) (snd r')).

Inductive type : Set :=
 | Sum : type -> type -> type
 | Prod : type -> type -> type
 | Arrow : stype -> type -> type -> type
 | Ref : rtype -> type -> type
 | Nat : type
 | Bool : type
 | Unit : type.

Fixpoint type_eqb (t t' : type) : bool :=
 match t, t' with
  | Sum t t', Sum u u' => andb (type_eqb t u) (type_eqb t' u')
  | Prod t t', Prod u u' => andb (type_eqb t u) (type_eqb t' u')

  | Arrow s t t', Arrow s' u u' =>
    andb (stype_eqb s s') (andb (type_eqb t u) (type_eqb t' u'))

  | Ref r t, Ref r' t' => (andb (rtype_eqb r r') (type_eqb t t'))
  | Nat, Nat => true
  | Bool, Bool => true
  | Unit, Unit => true
  | _, _ => false
 end.

Definition type_eqb_dec (t t' : type) :
 {Is_true (type_eqb t t')} + {~Is_true (type_eqb t t')}.

 intros t t'.
 destruct (type_eqb t t'); simpl Is_true.
 refine (left _ _); trivial.
 refine (right _ _); intuition.
Defined.

Theorem type_eq_eq : forall (t t' : type), Is_true (type_eqb t t') -> t = t'.

 induction t; destruct t'; simpl type_eqb; intro G;
 try (apply andb_prop_elim in G; intuition);
 try(apply IHt1 in H0; apply IHt2 in H1; rewrite H0; rewrite H1; reflexivity);
 try(elim G; intuition).

 apply stype_eqb_eq in H0; rewrite H0.
 apply andb_prop_elim in H1; intuition.
 apply IHt1 in H2; apply IHt2 in H3; rewrite H2; rewrite H3; reflexivity.

 unfold rtype_eqb in H0; apply andb_prop_elim in H0; intuition.
 destruct r. destruct r0.
 simpl fst in H2; simpl fst in H3; simpl snd in H2; simpl snd in H3.
 apply stype_eqb_eq in H2; apply stype_eqb_eq in H3.
 rewrite H2; rewrite H3. apply IHt in H1. rewrite H1. reflexivity.

Qed.


Definition sdot (r : rtype) (s : stype) : rtype :=
 match r with
  | (r, ir) => ((lub r s), (lub ir s))
 end.

Notation "r ** s" := (sdot r s) (no associativity, at level 50).

Theorem sdot_lub_canc : forall (r : rtype) (s s' : stype),
  ((r ** s) ** s') = (r ** (s |_| s')).

 destruct r as (u, v); destruct u; destruct v; destruct s; destruct s';
 compute; reflexivity.

Qed.

Fixpoint nat_eqb (n m : nat) : bool :=
 match n, m with
  | O, O => true
  | S n', S m' => nat_eqb n' m'
  | _, _ => false
 end.

Definition loc (t : type) : Set := nat.

Definition loc_eq (t t' : type) (l : loc t) (l' : loc t') : bool :=
 andb (nat_eqb l l') (type_eqb t t').

Notation "x == x'" := (loc_eq _ _ x x') (no associativity, at level 50).

Definition loc_eq_dec (t t' : type) (l : loc t) (l' : loc t') :
 {Is_true (l == l')} + {~Is_true (l == l')}.

 intros t t' l l'.
 destruct (loc_eq _ _ l l'); unfold Is_true.
 exact (left _ I).
 refine (right _ _). intuition.
Defined.

Theorem loc_eq_eq : forall (t t' : type) (l : loc t) (l' : loc t'),
 Is_true (l == l') -> l = l.

 intros t t' l l'.
 unfold loc_eq; intro G; apply andb_prop_elim in G; intuition.
Qed.


(*
   basically, this theorem is necessary for a typed environment
   that passes the Coq type inferencer
 *)
Theorem loc_eq_implies_type_eq : forall (t t' : type) (l : loc t) (l' : loc t'),
 Is_true (l == l') -> t = t'.

 intros t t' l l'.

 unfold loc_eq.
 intro G; apply andb_prop_elim in G. intuition.
 apply type_eq_eq in H1.
 exact H1.
Qed.

 
Fixpoint type_denote (t : type) : Set :=
 match t with
  | Sum t t' => ((type_denote t) + (type_denote t'))%type
  | Prod t t' => ((type_denote t) * (type_denote t'))%type
  | Arrow _ t t' => (type_denote t) -> (type_denote t')
  | Ref _ t => loc t
  | Nat => nat
  | Bool => bool
  | Unit => unit
 end.

(*
Inductive var : type -> Set :=
 | Var' : forall (t : type), nat -> var t.

Definition var_index (t : type) : var t -> nat :=
 fun (x : var t) =>
  match x with
   | Var' _ n => n
  end.
*)

Section expr.

 (* note to self: all the types declared above must be in 'Set' and not 'Type'
    or the definition of 'expr' below will incur the following error:

      Large non-propositional inductive types must be in Type.

    whatever the hell that means.
 *)

 Variable var : type -> Set.

 Inductive expr : type -> Set :=

  | Val : forall (t : type), rtype -> val t -> expr t
  | Var : forall (t : type), rtype -> var t -> expr t

  | InjL : forall (t t' : type), rtype -> expr t -> expr (Sum t t')
           
  | InjR : forall (t t' : type), rtype -> expr t' -> expr (Sum t t')

  | Cross : forall (t t' : type),
            rtype -> expr t -> expr t' -> expr (Prod t t')

  | Abs : forall (t t' : type) (s : stype),
          rtype -> var t -> expr t' -> expr (Arrow s t t')

  | App : forall (t t' : type) (s : stype),
          stype -> expr (Arrow s t t') -> expr t -> expr t'

  | Proj1 : forall (t t' : type),
            stype -> expr (Prod t t') -> expr t
  | Proj2 : forall (t t' : type),
            stype -> expr (Prod t t') -> expr t'

  | Case : forall (t t' t'' : type),
           stype ->
           expr (Sum t t') ->
           (var t -> expr t'') ->
           (var t' -> expr t'') ->
           expr t''

  | Read : forall (t : type) (r : rtype),
           stype -> expr (Ref r t) -> expr t

  | Write : forall (t : type) (r : rtype),
            expr (Ref r t) -> expr t -> expr t

(*
  | Mu : forall (t t' : type) (r : rtype),
         var (Arrow r t t')
         -> expr (Arrow r t t') -> expr (Arrow r t t')
*)
 with val : type -> Set :=
  | Inl : forall (t t' : type), val t -> val (Sum t t')
  | Inr : forall (t t' : type), val t' -> val (Sum t t')
  | Pair : forall (t t' : type),
           val t -> val t' -> val (Prod t t')
  | Loc : forall (t : type) (r : rtype), loc t -> val (Ref r t)
  | Num : nat -> val Nat
  | Bol : bool -> val Bool
  | TT : val Unit.


Definition typeof (t : type) (e : expr t) : type :=
 match e with
  | Val t _ _ => t
  | Var t _ _ => t
  | InjL t t' _ _ => Sum t t'
  | InjR t t' _ _ => Sum t t'
  | Cross t t' _ _ _ => Prod t t'
  | Abs t t' s _ _ _ => Arrow s t t'
  | App _ t' _ _ _ _ => t'
  | Proj1 t _ _ _ => t
  | Proj2 _ t' _ _ => t'
  | Case _ _ t'' _ _ _ _ => t''
  | Read t _ _ _ => t
  | Write t _ _ _ => t
 end.

(* access permission levels annotated to a term *)
Fixpoint perms (t : type) (e : expr t) : rtype :=

 match e with
  | Val _ r _ => r
  | Var _ r _ => r
  | InjL _ _ r _ => r
  | InjR _ _ r _ => r
  | Cross _ _ r _ _ => r
  | Abs _  _ _ r _ _ => r
  | App _ _ _ _ e _ => perms _ e
  | Proj1 _ _ _ e => perms _ e
  | Proj2 _ _ _ e => perms _ e
  | Case _ _ _ _ e _ _ => perms _ e
  | Read _ r _ _ => r
  | Write _ r _ _ => r 
 end.

Definition reader (t : type) (e : expr t) := fst (perms t e).
Definition ireader (t : type) (e : expr t) := snd (perms t e).

Notation "< e >" := (reader _ e) (no associativity, at level 10).
Notation "<< e >>" := (ireader _ e) (no associativity, at level 10).



Fixpoint val_denote (t : type) (v : val t) : type_denote t :=

 (* another case where 'match' needs all the extra syntax *)
 match v in (val t) return (type_denote t) with
  | Inl t t' v => inl (type_denote t') (val_denote t v)
  | Inr t t' v => inr (type_denote t) (val_denote t' v)
  | Pair t t' v v' => (val_denote t v, val_denote t' v')
  | Loc _ _ x => x
  | Num n => n
  | Bol b => b
  | TT => tt
 end.


End expr.


Definition protect (ir : stype) (t : type) (var : type -> Set) (e : expr var t)
 : expr var t :=

  match e with
   | Val t r v => Val var t (r ** ir) v
   | Var t r x => Var var t (r ** ir) x
   | InjL t t' r e => InjL var t t' (sdot r ir) e
   | InjR t t' r e => InjR var t t' (sdot r ir) e
   | Cross t t' r e e' => Cross var t t' (sdot r ir) e e'
   | Abs t t' s r x e => Abs var t t' s (sdot r ir) x e
   | e => e
  end.

Notation "e *** s" := (protect s _ _ e) (no associativity, at level 50).


Definition env' (var : type -> Set) (loc' : type -> Set) : Type :=
  forall (t : type), loc' t -> option (val var t).


Check (fun (var : type -> Set) => env' var loc).

Check
 (fun (var : type -> Set) (loc' : type -> Set) => env' var loc').


Inductive env (var : type -> Set) : Type :=
 | Empty : env var
 | Bind : forall (t : type), loc t -> val var t -> env var -> env var.

Notation "x :== v ::: rho" := (Bind x v rho) (right associativity, at level 60).

(* extend the environment with a new variable binding *)
Definition ext (t : type) (var : type -> Set) :
 forall (x : loc t) (v : val var t), env var -> env var :=
  fun (x : loc t) (v : val var t) (rho : env var) => Bind _ _ x v rho.

Notation "<< rho [ x |-> v ] >>" := (ext _ _ x v rho)
 (right associativity, at level 60).

Definition lkp (var : type -> Set) (t : type) (x : loc t) (rho : env var)
 : option (val var t).

 intros var t x rho.

 refine (

  (fix lkp (rho : env var) :=

  match rho with
   | Bind _ x' v rho' => if loc_eq_dec _ _ x x' then Some _ else lkp rho'
   | Empty => None
  end) rho

 ). clear lkp.

 assert (t = t0).
 apply loc_eq_implies_type_eq in _H.
 exact _H.

 rewrite <- H0 in v. exact v.
Defined.

(*
Check ((fun (var : type -> Set) (rho : env) =>
 (fun (t : type) (x : loc t) => (lkp t x rho)) : env' var loc)).
*)

Section expr_denote.

 Variable var : type -> Set.
 Variable loc' : type -> Set.

 (* represent mutable store as a two-level state monad of environments *)
 Definition Sto (a : Set) : Type := SepState (env' var loc) (env' var loc) a.

 Fixpoint expr_denote (rho : env var) (t : type) (e : expr type_denote t)
  : Sto (type_denote t) :=

  match e in (expr _ t) return (type_denote t) with
   | Val t _ v => ## (val_denote type_denote t v)
   | Var t _ x => ## x

   | InjL t t' _ e => expr_denote t e >>= fun v =>
                      ## (inl (type_denote t') v)

   | InjR t t' _ e => expr_denote t e >>= fun v =>
                      ## (inr (type_denote t) v)

   | Cross t t' _ e e' => expr_denote t e >>= fun v =>
                          expr_denote t e >>= fun v' =>
                          ## (v, v')

   | Abs _ _ t' _ _ f => fun s => ## (fun x => (expr_denote t' (f x)) s)

   | App _ _ _ _ e e' => expr_denote _ e >>= fun v =>
                         expr_denote _ e' >>= fun v'=>
                         ## (v v')

   | Proj1 t _ _ e => expr_denote _ e >>= fun v =>
                      ## (fst v)
   | Proj2 _ t' _ e => expr_denote _ e >>= fun v =>
                       ## (snd v)

   | Case t t' t'' r e f f' =>
     match (expr_denote _ e) with
      | inl x => expr_denote t'' (f x)
      | inr x => expr_denote t'' (f' x)
     end

   | Read t _ _ e => val_denote _ _ (lkp _ _ (expr_denote _ e) rho)

  end.
 


 Variable rho : (env type_denote).

 Fixpoint expr_denote (t : type) (e : expr type_denote t) : type_denote t :=

  match e in (expr _ t) return (type_denote t) with
   | Val t _ v => val_denote type_denote t v
   | Var t _ x => x
   | InjL t t' _ e => inl (type_denote t') (expr_denote t e)
   | InjR t t' _ e => inr (type_denote t) (expr_denote t' e)
   | Cross t t' _ e e' => (expr_denote t e, expr_denote t' e')
   | Abs _ t' _ _ f => fun x => expr_denote t' (f x)
   | App _ _ _ _ e e' => (expr_denote _ e) (expr_denote _ e')
   | Proj1 t _ _ e => fst (expr_denote _ e)
   | Proj2 _ t' _ e => snd (expr_denote _ e)

   | Case t t' t'' r e f f' =>
     match (expr_denote _ e) with
      | inl x => expr_denote t'' (f x)
      | inr x => expr_denote t'' (f' x)
     end

   | Read t _ _ e => val_denote _ _ (lkp _ _ (expr_denote _ e) rho)

  end.


End expr_denote.

(* distinguish constructors and destructors *)
Inductive ctor (var : type -> Set) : forall (t : type), expr var t -> Prop :=

 | CInjL : forall (t t' : type) (r : rtype) (e : expr var t),
           ctor var (Sum t t') (InjL var t t' r e)
 | CInjR : forall (t t' : type) (r : rtype) (e : expr var t'),
           ctor var (Sum t t') (InjR var t t' r e)

 | CCross : forall (t t' : type) (r : rtype)
                   (e : expr var t) (e' : expr var t'),
            ctor var (Prod t t') (Cross var t t' r e e')

 | CAbs : forall (t t' : type) (r : rtype) (f : var t -> expr var t'),
          ctor var (Arrow t t') (Abs var t t' r f).

Definition ctor_dec : forall (var : type -> Set) (t : type) (e : expr var t),
 {ctor var t e} + {~ctor var t e}.

 intros var t e.

 refine (

  match e with
   | InjL _ _ _ _ => _
   | InjR _ _ _ _ => _
   | Cross _ _ _ _ _ => _
   | Abs _ _ _ _ => _
   | _ => _
  end
 ).


 refine (right _ _). intuition. inversion H0.
 refine (right _ _). intuition. inversion H0.

 refine (left _ _). constructor.
 refine (left _ _). constructor.
 refine (left _ _). constructor.
 refine (left _ _). constructor.

 refine (right _ _). intuition. inversion H0.
 refine (right _ _). intuition. inversion H0.
 refine (right _ _). intuition. inversion H0.
 refine (right _ _). intuition. inversion H0.
Defined.


Inductive dtor (var : type -> Set) : forall (t : type), expr var t -> Prop :=

 | DProj1 : forall (t t' : type) (s : stype)
                   (e : expr var (Prod t t')),
            dtor var t (Proj1 var t t' s e)

 | DProj2 : forall (t t' : type) (s : stype)
                   (e : expr var (Prod t t')),
            dtor var t' (Proj2 var t t' s e)

 | DCase : forall (t t' t'' : type) (s : stype)
                  (e : expr var (Sum t t'))
                  (f : var t -> expr var t'')
                  (f' : var t' -> expr var t''),
           dtor var t'' (Case var t t' t'' s e f f')

 | DApp : forall (t t' : type) (s : stype)
                 (e : expr var (Arrow t t')) (e' : expr var t),
          dtor var t' (App var t t' s e e').


Definition dtor_dec : forall (var : type -> Set) (t : type) (e : expr var t),
 {dtor var t e} + {~dtor var t e}.

 intros var t e.

 refine (

  match e with
   | Proj1 _ _ _ _ => _
   | Proj2 _ _ _ _ => _
   | Case _ _ _ _ _ _ _ => _
   | App _ _ _ _ _ => _
   | _ => _
  end
 ).


 refine (right _ _). intuition. inversion H0.
 refine (right _ _). intuition. inversion H0.
 refine (right _ _). intuition. inversion H0.
 refine (right _ _). intuition. inversion H0.
 refine (right _ _). intuition. inversion H0.
 refine (right _ _). intuition. inversion H0.

 refine (left _ _). constructor.
 refine (left _ _). constructor.
 refine (left _ _). constructor.
 refine (left _ _). constructor.
Defined.


(* access the priviledges of a destructor *)

Definition priv (var : type -> Set) (t : type)
                (e : expr var t) : stype + {~dtor var t e}.

 intros var t.

 inversion e;

 refine (
  match e with
   | Proj1 _ _ s _ => inleft _ s
   | Proj2 _ _ s _ => inleft _ s
   | Case _ _ _ s _ _ _ => inleft _ s
   | App _ _ s _ _ => inleft _ s
   | _ => inright _ _
  end

 ); compute; inversion 1.

Defined.


(* no-write down policy as an inductive predicate *)


Inductive safe (var : type -> Set) : forall (t : type), expr var t -> Prop :=

 | SVal : forall (t : type) (v : val var t) (r : rtype),
          safe var t (Val var t r v)

 | SVar : forall (t : type) (x : var t) (r : rtype), safe var t (Var var t r x)

 | SInjL : forall (t' t'' : type) (r : rtype) (e : expr var t'),
           safe var t' e -> safe var (Sum t' t'') (InjL var t' t'' r e)
 | SInjR : forall (t' t'' : type) (r : rtype) (e : expr var t''),
           safe var t'' e -> safe var (Sum t' t'') (InjR var t' t'' r e)

 | SCross : forall (t' t'' : type) (r : rtype)
            (e : expr var t') (e' : expr var t''),
            safe var t' e ->
            safe var t'' e' ->
            safe var (Prod t' t'') (Cross var t' t'' r e e')

 | SAbs : forall (t' t'' : type) (r : rtype) (e : expr var t''),
          safe var t'' e ->
          safe var (Arrow t' t'') (Abs var t' t'' r (fun (x : var t') => e))

 (* these are the important cases *)
 | SApp : forall (t' t'' : type) (s : stype)
                 (e : expr var (Arrow t' t'')) (e' : expr var t'),
          safe var (Arrow t' t'') e ->
          safe var t' e' ->
          reader _ _ e |< s ->
          safe var t'' (App var t' t'' s e (e' *** (ireader _ _ e)))

 | SProj1 : forall (t' t'' : type) (s : stype)
                   (e : expr var (Prod t' t'')),
            safe var (Prod t' t'') e ->
            reader _ _ e |< s ->
            safe var t' (Proj1 var t' t'' s (e *** (ireader _ _ e)))

 | SProj2 : forall (t' t'' : type) (s : stype)
                   (e : expr var (Prod t' t'')),
            safe var (Prod t' t'') e ->
            reader _ _ e |< s ->
            safe var t'' (Proj2 var t' t'' s (e *** (ireader _ _ e)))

 | SCase : forall (t' t'' t''' : type) (s : stype)
                  (e : expr var (Sum t' t''))
                  (e' : expr var t''')
                  (e'' : expr var t'''),
           safe var (Sum t' t'') e ->
           safe var t''' e' ->
           safe var t''' e'' ->
           reader _ _ e |< s ->
           safe var t'''
            (Case var t' t'' t''' s e
              (fun (x : var t') => (e' *** (ireader _ _ e)))
              (fun (x : var t'') => (e'' *** (ireader _ _ e)))).
