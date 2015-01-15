(*
  this is ~/cheapthreads/CTC/CT-1.0/RPSLam/Mechanization/PHOAS.v

  a transition of the initial SLam mechanization into a style
  that exploits the verification advantages of Chlipala's PHOAS;

  situated to become the source for the POPL'12 work;

  plus I'm ditching the annotations-as-dependent-types, since it makes
  every damn function definition a total cluster-fuck (2011.05.08).

  See "Certified Programming with Dependent Types" (17.2) [Chlipala]
  for more details

  branched 2011.05.24 from the version 2011.05.02

  basic idea behind the cleanup is to define a clean separation between
  the annotations and the underlying calculus, which will hopefully
  ameliorate the serious proof challenges presented by defining a semantics
  that (implicitly) depends on the semantcs.

  Steps:

  (1) Define the annotated calculus;
  (2) Define transformations that separate an annotated term into
      an unannotated term (the semantics for which are unproblematic)
      and a structure expressing the assertions of the annotations themselves;
  (3) [in a different/future module] Show that terms whose annotation shadow
      satisfies a safety predicate compile to object terms satisfying a
      comparable predicate.

  Schulz
*)

Require Import Arith.
Require Import Bool.
Require Import List.

Import StateT.



Section stype.

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

End stype.



Section type.

Variable sto : Type.

Inductive type : Set :=
 | Sum : type -> type -> type
 | Prod : type -> type -> type
 | Arrow : type -> type -> type
 | RefT : rtype -> type -> type
 | Nat : type
 | Bool : type
 | Unit : type.

Fixpoint type_eqb (t t' : type) : bool :=
 match t, t' with
  | Sum t t', Sum u u' => andb (type_eqb t u) (type_eqb t' u')
  | Prod t t', Prod u u' => andb (type_eqb t u) (type_eqb t' u')

  | Arrow t t', Arrow u u' =>
    andb (type_eqb t u) (type_eqb t' u')

  | RefT r t, RefT r' t' => (andb (rtype_eqb r r') (type_eqb t t'))
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

(*
 apply stype_eqb_eq in H0; rewrite H0.
 apply andb_prop_elim in H1; intuition.
 apply IHt1 in H2; apply IHt2 in H3; rewrite H2; rewrite H3; reflexivity.
*)

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
  ((r ** s) ** s') = (r ** (lub s s')).

 destruct r as (u, v); destruct u; destruct v; destruct s; destruct s';
 compute; reflexivity.

Qed.

Fixpoint nat_eqb (n m : nat) : bool :=
 match n, m with
  | O, O => true
  | S n', S m' => nat_eqb n' m'
  | _, _ => false
 end.

Print sumbool.

Definition nat_eq_dec :
 forall (n m : nat), {Is_true (nat_eqb n m)} + {~Is_true (nat_eqb n m)}.

 intros n m.
 destruct (nat_eqb n m); simpl Is_true.
 left; trivial.
 right; intuition.
Defined.
 

Definition loc (t : type) (r : rtype) : Set := nat.

Definition loc_index (t : type) (r : rtype) (l : loc t r) : nat := l.

Definition loc_eq
 (t t' : type) (r r' : rtype) (l : loc t r) (l' : loc t' r') : bool :=
 andb (nat_eqb l l') (andb (rtype_eqb r r') (type_eqb t t')).

Notation "x == x'" := (loc_eq _ _ _ _ x x') (no associativity, at level 50).

Definition loc_eq_dec
 (t t' : type) (r r' : rtype) (l : loc t r) (l' : loc t' r') :
 {Is_true (l == l')} + {~Is_true (l == l')}.

 intros t t' r r' l l'.
 destruct (loc_eq _ _ _ _ l l'); unfold Is_true.
 exact (left _ I).
 refine (right _ _). intuition.
Defined.

Implicit Arguments loc_eq_dec [t t' r r'].

Theorem loc_eq_eq :
 forall (t t' : type) (r r' : rtype) (l : loc t r) (l' : loc t' r'),
 Is_true (l == l') -> l = l.

 intros t t' r r' l l'.
 unfold loc_eq; intro G; apply andb_prop_elim in G; intuition.
Qed.


(*
   basically, this theorem is necessary for a typed heapironment
   that passes the Coq type inferencer
 *)
Theorem loc_eq_implies_type_eq :
forall (t t' : type) (r r' : rtype) (l : loc t r) (l' : loc t' r'),
 Is_true (l == l') -> t = t'.

 intros t t' r r' l l'.

 unfold loc_eq.
 intro G; apply andb_prop_elim in G. intuition.
 apply andb_prop_elim in H1. intuition.
 apply type_eq_eq in H3.
 exact H3.
Qed.



Inductive val : Type -> Type :=
 | VSum : forall (t t' : Type), val (t + t')
 | VProd : forall (t t' : Type), val (t * t')
 | VArrow : forall (t t' : Type), val (t -> t')
 | VRef : forall (t : type) (r : rtype), val (loc t r)
 | VNat : val nat
 | VBool : val bool
 | VUnit : val unit.

Fixpoint val_denote (T : Type) (v : val T) : Type :=
 match v with
  | VSum t t' => (t + t')%type
  | VProd t t' => (t * t')%type
  | VArrow t t' => t -> t'
  | VRef r t => loc r t
  | VNat => nat
  | VBool => bool
  | VUnit => unit
 end.


Inductive heap : Type :=
 | Empty : heap
 | Up : forall (t : type) (r : rtype) (T : Type),
        val T -> loc t r -> heap -> heap.


Fixpoint type_denote (t : type) :=
 match t with
  | Sum t t' => ((type_denote t) + (type_denote t'))%type
  | Prod t t' => ((type_denote t) * (type_denote t'))%type
  | Arrow t t' => ((type_denote t) -> SepState sto sto (type_denote t'))
  | RefT r t => (loc t r)
  | Nat => nat
  | Bool => bool
  | Unit => unit
 end.


Definition teval (t : type) : (val (type_denote t)).

 intro t.

 refine (
  match t return (val (type_denote t)) with
   | Sum t t' => VSum _ _
   | Prod t t' => VProd _ _
   | Arrow t t' => VArrow _ _ 
   | RefT r t => VRef _ _
   | Nat => VNat
   | Bool => VBool
   | Unit => VUnit
  end
 ).
Defined.

Check type_denote.

Theorem val_type_eq : forall (t : type), type_denote t = val_denote _ (teval t).

 induction t; simpl type_denote.

blah blah blah (* syntax error to find my place *)

 simpl teval.


End type.


Section heap.
 

Definition isempty (rho : heap) : Prop :=
 match rho with
  | Empty => True
  | _ => False
 end.


Definition empty_dec : forall (rho : heap), {isempty rho} + {~isempty rho}.

 destruct rho.
 refine (left _ _); simpl isempty; trivial.
 refine (right _ _); simpl isempty; intuition.
Defined.



Fixpoint size (rho : heap) : nat :=
 match rho with
  | Empty => O
  | Up _ _ _ _ _ rho' => S (size rho')
 end.

End heap.







Section expr.

 (* note to self: all the types declared above must be in 'Set' and not 'Type'
    or the definition of 'expr' below will incur the following error:

      Large non-propositional inductive types must be in Type.

    whatever the hell that means.
 *)
 Variable var : type -> Type.

 (* annotated syntax *)
 Inductive sexpr : type -> Type :=

  | SNConst : rtype -> nat -> sexpr Nat
  | SBConst : rtype -> bool -> sexpr Bool
  | SUConst : rtype -> sexpr Unit

  | SVar : forall (t : type), rtype -> var t -> sexpr t

  | SInjL : forall (t t' : type), rtype -> sexpr t -> sexpr (Sum t t')
           
  | SInjR : forall (t t' : type), rtype -> sexpr t' -> sexpr (Sum t t')

  | SCross : forall (t t' : type),
             rtype -> sexpr t -> sexpr t' -> sexpr (Prod t t')

  | SAbs : forall (t t' : type),
           rtype -> (var t -> sexpr t') -> sexpr (Arrow t t')

  | SApp : forall (t t' : type),
           stype -> rtype -> sexpr (Arrow t t') -> sexpr t -> sexpr t'

  | SProj1 : forall (t t' : type),
             stype -> rtype -> sexpr (Prod t t') -> sexpr t
  | SProj2 : forall (t t' : type),
             stype -> rtype -> sexpr (Prod t t') -> sexpr t'

  | SCase : forall (t t' t'' : type),
            stype -> rtype ->
            sexpr (Sum t t') ->
            (var t -> sexpr t'') ->
            (var t' -> sexpr t'') ->
            sexpr t''

  | SRef : forall (t : type) (r : rtype),
           sexpr t -> sexpr (RefT r t)

  | SDeref : forall (t : type) (r : rtype),
             stype -> sexpr (RefT r t) -> sexpr t

  | SAssign : forall (t : type) (r : rtype),
              stype -> sexpr (RefT r t) -> sexpr t -> sexpr t.


 (* unannotated syntax *)
 Inductive expr : type -> Type :=

  | NConst : nat -> expr Nat
  | BConst : bool -> expr Bool
  | UConst : expr Unit

  | Var : forall (t : type), var t -> expr t

  | Abs : forall (t t' : type),
          (var t -> expr t') -> expr (Arrow t t')

  | Cross : forall (t t' : type), expr t -> expr t' -> expr (Prod t t')

  | InjL : forall (t t' : type), expr t -> expr (Sum t t')
  | InjR : forall (t t' : type), expr t' -> expr (Sum t t')


  | App : forall (t t' : type),
          expr (Arrow t t') -> expr t -> expr t'

  | Proj1 : forall (t t' : type), expr (Prod t t') -> expr t

  | Proj2 : forall (t t' : type), expr (Prod t t') -> expr t'

  | Case : forall (t t' t'' : type),
            expr (Sum t t') ->
            (var t -> expr t'') ->
            (var t' -> expr t'') ->
            expr t''

  | Ref : forall (t : type) (r : rtype), expr t -> expr (RefT r t)

  | Deref : forall (t : type) (r : rtype), expr (RefT r t) -> expr t

  | Assign : forall (t : type) (r : rtype), expr (RefT r t) -> expr t -> expr t.



 (* erasure of the annotations *)
 Fixpoint erase (t : type) (e : sexpr t) : expr t :=

  match e in (sexpr t) return (expr t) with
   | SNConst _ n => NConst n
   | SBConst _ b => BConst b
   | SUConst _ => UConst

   | SVar t _ x => Var t x

   | SInjL t t' _ e' => InjL t t' (erase _ e')
   | SInjR t t' _ e' => InjR t t' (erase _ e')
   | SCross t t' _ e' e'' => Cross t t' (erase _ e') (erase _ e'')

   | SAbs t t' _ f => Abs t t' (fun x => erase _ (f x))
   | SApp t t' _ _ f e' => App t t' (erase _ f) (erase _ e')
      

   | SProj1 t t' _ _ e' => Proj1 t t' (erase _ e')
   | SProj2 t t' _ _ e' => Proj2 t t' (erase _ e')
   | SCase t t' t'' _ _ e' f f' =>
      Case t t' t'' (erase _ e')
      (fun x => erase _ (f x)) (fun x => erase _ (f' x))

   | SRef t r e' => Ref t r (erase _ e')
   | SDeref t r _ e' => Deref t r (erase _ e')
   | SAssign t r _ e' e'' => Assign t r (erase _ e') (erase _ e'')
  end.

End expr.

(* un-syntaxed annotations *)
Section aexpr.

 Variable var : type -> Type.

 Inductive aexpr : Type :=

  | AConst : rtype -> aexpr
  | AVar : rtype -> aexpr

  | ACross : rtype -> aexpr -> aexpr -> aexpr

  | AInj : rtype ->  aexpr -> aexpr

  | AAbs : forall (t : type), rtype -> (var t -> aexpr) -> aexpr

  | AApp : stype -> rtype -> aexpr -> aexpr -> aexpr

  | AProj : stype -> rtype -> aexpr -> aexpr

  | ACase : forall (t t' : type),
            stype ->
            rtype -> 
            aexpr -> 
            (var t -> aexpr) ->
            (var t' -> aexpr) -> aexpr

  | ARef : rtype -> aexpr -> aexpr
           
  | ADeref : rtype -> stype -> aexpr -> aexpr

  | AAssign : rtype -> stype -> aexpr -> aexpr -> aexpr.



 Fixpoint extract (t : type) (e : sexpr var t) : aexpr :=
  match e with 
   | SNConst r _ => AConst r
   | SBConst r _ => AConst r
   | SUConst r => AConst r

   | SVar _ r _ => AVar r
   | SInjL _ _ r e' => AInj r (extract _ e')
   | SInjR _ _ r e' => AInj r (extract _ e')
   | SCross _ _ r e' e'' => ACross r (extract _ e') (extract _ e'')
   | SAbs _ _ r f => AAbs _ r (fun x => (extract _ (f x)))

   | SApp _ _ s r f e' => AApp s r (extract _ f) (extract _ e')
   | SProj1 _ _ s r e' => AProj s r (extract _ e')
   | SProj2 _ _ s r e' => AProj s r (extract _ e')
   | SCase _ _ _ s r e' f f' =>
      ACase _ _ s r (extract _ e')
       (fun x => (extract _ (f x))) (fun x => (extract _ (f' x)))

   | SRef _ r e' => ARef r (extract _ e')
   | SDeref _ r s e' => ADeref r s (extract _ e')
   | SAssign _ r s e' e'' => AAssign r s (extract _ e') (extract _ e'')

  end.



Definition stV (a b c : Set) : a * b * c -> a :=
 fun x =>
 match x with
  | (v, _, _) => v
 end.

Definition stL (a b c : Set) : a * b * c -> b :=
 fun x =>
 match x with
  | (_, v, _) => v
 end.

Definition stR (a b c : Set) : a * b * c -> c :=
 fun x =>
 match x with
  | (_, _, v) => v
 end.

Implicit Arguments stV [a b c].
Implicit Arguments stL [a b c].
Implicit Arguments stR [a b c].

(* state monad operations used to implement mutable references *) 
Definition Sto (sto a : Type) : Type := SepState sto sto a.

Definition type_denote' := type_denote.

Theorem type_denote_id : type_denote = type_denote'.
 unfold type_denote'. reflexivity.
Qed.

Check heap.
Check type_denote.
Print type_denote.
Print heap.

Definition Heap : Type := heap.


Fixpoint size' (rho : Heap) : nat :=
 match rho with
  | Empty => O
  | Up _ _ _ _ _ rho' => S (size' rho')
 end.


Definition lkp
 (t : type) (r : rtype) (l : loc t r) (h : Heap) : option (type_denote type t).

 intros t r l h.

 Print Up.

 refine (

  (fix lkp (h' : Heap) :=

   match h' with
    | Empty => None
    | Up t' r' _ v l' h'' =>
       if loc_eq_dec t t' r r' l l' then Some _ else lkp h''
   end
  ) h

 ).

 apply loc_eq_implies_type_eq in _H.
 destruct v. unfold val in v. rewrite <- _H in v.
 rewrite <- type_denote_id in v. exact v.
Defined.


Definition St (a : Type) : Type := Sto Heap a.


Notation "x >>= f" := (bind_sep _ _ _ _ x f)
 (no associativity, at level 20).

Notation "## v" := (eta_sep _ _ _ v)
  (no associativity, at level 10).


Definition alloc (t : type) (r : rtype) :=

 (match r with
   | (L, _) => get_L Heap Heap
   | (H, _) => get_R Heap Heap
  end
 ) >>= fun h => ## (S (size' h)).


Fixpoint store'
 (h : Heap) (t : type) (r : rtype) (v : type_denote type t) (l : loc t r)
 : Heap :=
 match h with
  | Empty => Empty _
  | Up t' r' v' l' h' =>
    if (loc_eq_dec t t' r r' l l')
    then Up _ t r v l' h'
    else Up _ t' r' v' l' (store' h' t r v l)
 end.


Definition store
 (t : type) (r : rtype) (v : type_denote type t) (l : loc t r) : St unit :=
 get_L Heap Heap >>= fun h => put_L Heap Heap (store' h t r v l).

Check lkp. 

Check type_denote.

Definition read
 (t : type) (r : rtype) (l : loc t r) : St (option (type_denote type t)) :=
 get_L Heap Heap >>= fun h => ## (lkp t r l h).


Notation "### v" := (## (Some v)) (no associativity, at level 10).
Notation "x >>>= f" :=
 (x >>= fun v =>
  match v with
   | Some v' => f v'
   | None => ## None
  end)
 (left associativity, at level 20).

Definition expr_denote (t : type) (e : expr (type_denote type) t) :
 St (option (type_denote type t)).

 intros t e.

 Print St.
 Print Sto.
 Print Heap.
 Print heap.

 refine (

 (fix expr_denote (t : type) (e : expr (type_denote type) t) :
  St (option (type_denote type t)) :=

 match e in (expr _ t) return (St (option (type_denote type t))) with
  | NConst n => ### n
  | BConst b => ### b
  | UConst => ### tt

  | Var _ x => ### x

  | Abs _ _ f => _

  | Cross _ _ e' e'' => _
  | InjL t t' e' => _
  | InjR t t' e' => _
  | App _ _ f e => _
  | Proj1 _ _ e' => _
  | Proj2 _ _ e' => _
  | Case _ _ _ e' f f' => _
  | Ref t _ e' => _
  | Deref t _ e' => _
  | Assign _ _ e' e'' => _
 end
  ) t e

  (* 
  | Cross _ _ e' e'' => expr_denote _ e' >>= fun v =>
                        expr_denote _ e'' >>= fun v' =>
                        ##(v, v')

  | InjL t t' e' => expr_denote _ e' >>= fun v =>
                    ## (inl (type_denote type t') v)

  | InjR t t' e' => expr_denote _ e' >>= fun v =>
                    ## (inr (type_denote type t) v)

  | App _ _ f e' => expr_denote _ f >>= fun f' =>
                    expr_denote _ e' >>= fun v =>
                    f' v

  | Proj1 _ _ e' => expr_denote _ e' >>= fun v => ## (fst v)
  | Proj2 _ _ e' => expr_denote _ e' >>= fun v => ## (snd v)
  | Case _ _ _ e' f f' =>
     expr_denote _ e' >>= fun d =>
     match d with
      | inl x => expr_denote _ (f x)
      | inr x => expr_denote _ (f' x)
     end
  | Ref t _ e' => alloc t >>= fun l =>
                  expr_denote _ e' >>= fun v =>
                  store t v l >>= fun _ =>
                  ## l

  | Deref t _ e' => expr_denote _ e' >>= fun l =>
                    read t l

  | Assign _ _ e' e'' => expr_denote e' >>= fun l =>
                         expr_denote e'' >>= fun v =>
                         store v l >>= fun _ =>
                         ## v


 end
 *)

 ).

 (* abstraction case *)
 simpl type_denote.
 exact (### (fun x => expr_denote _ (f x))).


(* distinguish constructors and destructors *)
Inductive ctor : aexpr -> Prop :=

 | CInj : forall (r : rtype) (e : aexpr),
           ctor (AInj r e)

 | CCross : forall (r : rtype) (e e' : aexpr),
            ctor (ACross r e e')

 | CAbs : forall (r : rtype) (t : type) (f : var t -> aexpr),
          ctor (AAbs _ r f).

Definition ctor_dec : forall (e : aexpr), {ctor e} + {~ctor e}.

 intro e.

 refine (

  match e with
   | AInj _ _ => _
   | ACross _ _ _ => _
   | AAbs _ _ _ => _
   | _ => _
  end
 ).


 refine (right _ _). intuition. inversion H0.
 refine (right _ _). intuition. inversion H0.

 refine (left _ _). constructor.
 refine (left _ _). constructor.
 refine (left _ _). constructor.

 refine (right _ _). intuition. inversion H0.
 refine (right _ _). intuition. inversion H0.
 refine (right _ _). intuition. inversion H0.
Defined.



Inductive dtor : aexpr -> Prop :=

 | DProj : forall (s : stype) (r : rtype) (e : aexpr), dtor (AProj s r e)

 | DCase : forall (s : stype) (r : rtype) (e : aexpr) (t t' : type)
                  (f : var t -> aexpr)
                  (f' : var t' -> aexpr),
           dtor (ACase _ _ s r e f f')

 | DApp : forall (s : stype) (r : rtype) (e e' : aexpr),
          dtor (AApp s r e e').


Definition dtor_dec (e : aexpr) : {dtor e} + {~dtor e}.
 
 intro e.

 refine (

  match e with
   | AProj _ _ _ => _
   | ACase _ _ _ _ _ _ _ => _
   | AApp _ _ _ _ => _
   | _ => _
  end
 ).


 refine (right _ _). intuition. inversion H0.
 refine (right _ _). intuition. inversion H0.
 refine (right _ _). intuition. inversion H0.
 refine (right _ _). intuition. inversion H0.
 refine (right _ _). intuition. inversion H0.

 refine (left _ _). constructor.
 refine (left _ _). constructor.
 refine (left _ _). constructor.

Defined.


(* access the priviledges of a destructor *)

Definition priv (e : aexpr) : stype + {~dtor e}.

 inversion e;

 refine (
  match e with
   | AProj s _ _ => inleft _ s
   | ACase _ _ s _ _ _ _ => inleft _ s
   | AApp s _ _ _ => inleft _ s
   | _ => inright _ _
  end

 ); compute; inversion 1.

Defined.

(* access permission level annotated to a term *)
Definition perms (e : aexpr) : rtype :=

 match e with
  | AConst r => r
  | AVar r => r
  | AInj r _ => r
  | ACross  r _ _ => r
  | AAbs _ r _ => r
  | AApp _ r _ _ => r
  | AProj _ r _ => r
  | ACase _ _ _ r _ _ _ => r
 end.

Definition reader (e : aexpr) := fst (perms e).
Definition ireader (e : aexpr) := snd (perms e).

Notation "< e >" := (reader _ e) (no associativity, at level 10).
Notation "<< e >>" := (ireader _ e) (no associativity, at level 10).

(* raise permissions; this is as in [Heintze-Riecke 1998] *)
Definition protect (ir : stype) (e : aexpr) : aexpr :=

  match e with
   | AConst r => AConst (r ** ir)
   | AVar r => AVar (r ** ir)
   | AInj r e' => AInj (r ** ir) e'
   | ACross r e' e'' => ACross (r ** ir) e' e''
   | AAbs t r f => AAbs t (r ** ir) f
   | AApp s r e' e'' => AApp s (r ** ir) e' e''
   | AProj s r e' => AProj s (r ** ir) e'
   | ACase t t' s r e' f f' => ACase t t' s (r ** ir) e' f f'
  end.

Notation "e *** s" := (protect s _ _ e) (no associativity, at level 50).


(* predicate expressing the information flow policy *)
Inductive safe : aexpr -> Prop :=
 | TConst : forall (r : rtype), safe (AConst r)
 | TVar : forall (r : rtype), safe (AVar r)
 | TCross : forall (r : rtype) (e e' : aexpr),
            safe e -> safe e' -> safe (ACross r e e')
 | TInj : forall (r : rtype) (e : aexpr),
          safe e -> safe (AInj r e)
 | TAbs : forall (r : rtype) (t : type) (e : aexpr),
          safe e -> safe (AAbs _ r (fun (x : var t) => e))

 | TApp : forall (s : stype) (r : rtype) (e e' : aexpr),
          safe e -> safe e' -> (reader e |< s) ->
          safe (AApp s (r ** ireader e) e e')

 | TProj : forall (s : stype) (r : rtype) (e : aexpr),
           safe e -> (reader e |< s) -> safe (AProj s (r ** ireader e) e)

 | TCase : forall (s : stype) (r : rtype) (e e' e'' : aexpr) (t t' : type),
           safe e -> (reader e |< s) ->
           safe e' -> safe e'' ->
           safe (ACase t t' s (r ** ireader e) e (fun x => e'') (fun x => e'')).
 

End aexpr.


(* everything up to this point is current 2011.05.26 *)


(*

  | Read : forall (t : type) (r : rtype),
           stype -> expr (RefT r t) -> expr t

  | Write : forall (t : type) (r : rtype),
            expr (RefT r t) -> expr t -> expr t

  | Mu : forall (t t' : type) (r : rtype),
         var (Arrow r t t')
         -> expr (Arrow r t t') -> expr (Arrow r t t')

 with val : type -> Set :=
  | Inl : forall (t t' : type), val t -> val (Sum t t')
  | Inr : forall (t t' : type), val t' -> val (Sum t t')
  | Pair : forall (t t' : type),
           val t -> val t' -> val (Prod t t')
  | Loc : forall (t : type) (r : rtype), loc t -> val (RefT r t)
  | Num : nat -> val Nat
  | Bol : bool -> val Bool
  | TT : val Unit.
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
          rtype -> (var t -> expr t') -> expr (Arrow s t t')

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
           stype -> expr (RefT r t) -> expr t

  | Write : forall (t : type) (r : rtype),
            expr (RefT r t) -> expr t -> expr t

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
  | Loc : forall (t : type) (r : rtype), loc t -> val (RefT r t)
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
  | Abs t t' s _ _ => Arrow s t t'
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
  | Abs _ _ _ r _ => r
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
   | Abs t t' s r f => Abs var t t' s (sdot r ir) f
   | e => e
  end.

Notation "e *** s" := (protect s _ _ e) (no associativity, at level 50).


Definition heap' (var : type -> Set) (loc' : type -> Set) : Type :=
  forall (t : type), loc' t -> option (val var t).


Check (fun (var : type -> Set) => heap' var loc).

Check
 (fun (var : type -> Set) (loc' : type -> Set) => heap' var loc').


Inductive heap (var : type -> Set) : Type :=
 | Empty : heap var 
 | Bind : forall (t : type), loc t -> val var t -> heap var -> heap var.

Notation "x :== v ::: rho" := (Bind x v rho) (right associativity, at level 60).

(* extend the heapironment with a new variable binding *)
Definition ext (t : type) (var : type -> Set) :
 forall (x : loc t) (v : val var t), heap var -> heap var  :=
  fun (x : loc t) (v : val var t) (rho : heap var) => Bind _ _ x v rho.

Notation "<< rho [ x |-> v ] >>" := (ext _ _ x v rho)
 (right associativity, at level 60).

Definition lkp (t : type) (var : type -> Set) (x : loc t) (rho : heap var)
 : option (val var t).

 intros t var x rho.

 refine (

  (fix lkp (rho : (heap var)) :=

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

Check ((fun (var : type -> Set) (rho : heap var) =>
 (fun (t : type) (x : loc t) => (lkp t var x rho)) : heap' var loc)).



Section expr_denote.

 Variable var : type -> Set.
 Variable loc' : type -> Set.

 (* represent mutable store as a two-level state monad of heapironments *)
 Definition Sto (a : Set) : Type := SepState (heap' var loc) (heap' var loc) a.


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
