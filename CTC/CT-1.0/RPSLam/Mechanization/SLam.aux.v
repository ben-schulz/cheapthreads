(*
  this is ~/cheapthreads/ctc_working/CT-1.0/RPSLam/Mechanization/SLam.v

  A Coq specifiation for the secure lambda calculus (SLam) as presented
  in [Heintze, Riecke 1998], and mechanization of some useful theorems
  about it.

  Put here 2010.03.14

  Schulz
*)


Require Import Logic.
Require Import List.
Require Import Arith.
Require Import Bool.
Require Import Tactics.


Inductive stype : Set :=
 | H : stype
 | L : stype.

Definition stype_eqb (s s' : stype) : bool :=
 match s, s' with
  | H, H => true
  | L, L => true
  | _, _ => false
 end.

Inductive stype_eq : stype -> stype -> Prop :=
 | HEq : stype_eq H H
 | LEq : stype_eq L L.


Theorem stype_eqb_refl : forall (s : stype), stype_eqb s s = true.

 destruct s; simpl; reflexivity.
Qed.

Theorem stype_eq_eq : forall (s s' : stype),
 Is_true (stype_eqb s s') -> stype_eq s s'.

 intros s s'.
 destruct s; destruct s'; simpl stype_eqb; unfold Is_true; intuition.
 constructor. constructor.
Qed.
 

(* partial order on the two-level domain *)
Definition slow (s1 s2 : stype) : bool :=
 match (s1, s2) with
  | (H, L) => false
  | _ => true
 end.

Definition pslow (s1 s2 : stype) : Prop := if slow s1 s2 then True else False.

Definition lub (s1 s2 : stype) : stype :=
 match (s1, s2) with
  | (H, _) => H
  | (_, H) => H
  | _ => L
 end.

Theorem lub_comm : forall s1 s2 : stype, lub s1 s2 = lub s2 s1.

 destruct s1; destruct s2.
 unfold lub; simpl; reflexivity.
 unfold lub; simpl; reflexivity.
 unfold lub; simpl; reflexivity.
 unfold lub; simpl; reflexivity.
Qed.

Definition rtype : Set := (stype * stype)%type.

Definition rtype_eqb (r r' : rtype) : bool :=
 match r, r' with
  | (x, x'), (y, y') => andb (stype_eqb x y) (stype_eqb x' y')
 end.

Inductive rtype_eq : rtype -> rtype -> Prop :=
 | RTEq : forall (x x' y y' : stype),
   stype_eq x x' -> stype_eq y y' -> rtype_eq (x, y) (x', y').


Theorem rtype_eqb_refl : forall (r : rtype), rtype_eqb r r = true.

  destruct r; unfold rtype_eqb; repeat (rewrite stype_eqb_refl); intuition.
Qed.
  

Definition sdot (r : rtype) (s : stype) : rtype :=
 match r with
  | (r, ir) => ((lub r s), (lub ir s))
 end.


Inductive vtype : Set :=
 | TSum : rtype -> vtype -> vtype -> vtype
 | TProd : rtype -> vtype -> vtype -> vtype
 | TArrow : rtype -> vtype -> vtype -> vtype
 | TNum : rtype -> vtype
 | TBool : rtype -> vtype
 | TUnit : rtype -> vtype.

Fixpoint vtype_denote (t : vtype) : Set :=
 match t with
  | TSum _ t' t'' => ((vtype_denote t') + (vtype_denote t''))%type
  | TProd _ t' t'' => ((vtype_denote t') * (vtype_denote t''))%type
  | TArrow _ t' t'' => (vtype_denote t') -> (vtype_denote t'')
  | TNum _ => nat
  | TBool _ => bool
  | TUnit _ => unit
 end.

Fixpoint vtype_eqb (t t' : vtype) : bool :=
 match t, t' with
  | (TSum r v v'), (TSum r' u u') =>
    andb (rtype_eqb r r') (andb (vtype_eqb v u) (vtype_eqb v' u'))
  | (TProd r v v'), (TProd r' u u') =>
    andb (rtype_eqb r r') (andb (vtype_eqb v u) (vtype_eqb v' u'))
  | (TArrow r v v'), (TArrow r' u u') =>
    andb (rtype_eqb r r') (andb (vtype_eqb v u) (vtype_eqb v' u'))
  | (TNum r), (TNum r') => rtype_eqb r r'
  | (TBool r), (TBool r') => rtype_eqb r r'
  | (TUnit r), (TUnit r') => rtype_eqb r r'
  | _, _ => false
 end.

Inductive vtype_eq : vtype -> vtype -> Prop :=
 | EqSum : forall (x x' y y' : vtype) (r r' : rtype),
    vtype_eq x x' ->  vtype_eq y y' -> rtype_eq r r' ->
    vtype_eq (TSum r x y) (TSum r' x' y)

 | EqProd : forall (x x' y y' : vtype) (r r' : rtype),
    vtype_eq x x' ->  vtype_eq y y' -> rtype_eq r r' ->
    vtype_eq (TProd r x y) (TProd r' x' y)

 | EqArrow : forall (x x' y y' : vtype) (r r' : rtype),
    vtype_eq x x' ->  vtype_eq y y' -> rtype_eq r r' ->
    vtype_eq (TArrow r x y) (TArrow r' x' y)

 | EqNum : forall (r r' : rtype), rtype_eq r r' -> vtype_eq (TNum r') (TNum r')

 | EqBool : forall (r r' : rtype),
   rtype_eq r r' -> vtype_eq (TBool r') (TBool r')

 | EqUnit : forall (r r' : rtype),
   rtype_eq r r' -> vtype_eq (TUnit r') (TUnit r').
 
Definition rtypeof (t : vtype) : rtype :=
 match t with
  | TSum r _ _ => r
  | TProd r _ _ => r
  | TArrow r _ _ => r
  | TNum r => r
  | TBool r => r
  | TUnit r => r
 end.


Definition reader (t : vtype) : stype := fst (rtypeof t).
Definition ireader (t : vtype) : stype := snd (rtypeof t).

Definition dot (t : vtype) (s : stype) :=
 match t with
  | TSum r t' t'' => TSum (sdot r s) t' t''
  | TProd r t' t'' => TProd (sdot r s) t' t''
  | TArrow r t' t'' => TArrow (sdot r s) t' t''
  | TNum r => TNum (sdot r s)
  | TBool r => TBool (sdot r s)
  | TUnit r => TUnit (sdot r s)
 end.



Definition vtype_eqb_dec : forall (t t' : vtype),
  {Is_true (vtype_eqb t t')} + {~ Is_true (vtype_eqb t t')}.

 intros t t'.
 destruct (vtype_eqb t t').

 simpl. refine (left _ _). trivial.
 simpl. refine (right _ _). intuition.
Qed.



Notation "< t >" := (reader t).
Notation "<< t >>" := (ireader t).
Notation "k ** s" := (dot k s) (right associativity, at level 60).

(* changing security annotation does not affect type denotation *)
Theorem vtype_annot_erase : forall (t : vtype) (s : stype),
 vtype_denote t  = vtype_denote (t ** s).

 induction t; intro s; simpl vtype_denote; trivial.

Qed.


Inductive var : vtype -> Set :=
 | Var : forall (t : vtype), nat -> var t.

Definition var_index (t : vtype) : var t -> nat :=
 fun (x : var t) =>
  match x with
   | Var _ n => n
  end.

Fixpoint nat_eq (n m : nat) : bool :=
 match n, m with
  | O, O => true
  | S n', S m' => nat_eq n' m'
  | _, _ => false
 end.


Definition vartype : forall (t : vtype), var t -> vtype :=

 fun (t : vtype) (x : var t) =>
  match x with
   | Var t _ => t
  end.
 
Definition var_eq (t t' : vtype) : var t -> var t' -> bool :=
 fun (x : var t) (x' : var t') =>
  ((nat_eq (var_index t x) (var_index t' x'))
   && (vtype_eqb (vartype t x) (vartype t' x')))%bool.

Notation "x == x'" := (var_eq _ _ x x') (no associativity, at level 60).


Definition var_eq_dec : forall (t t' : vtype) (x : var t) (x' : var t'),
 {Is_true (x == x')} + {~ Is_true (x == x')}.

 intros t t' x x'.
 destruct (x == x'); unfold Is_true.
 refine (left _ _); trivial.
 refine (right _ _); intuition.
Defined.

Theorem rtype_eqb_eq : forall (r r' : rtype), Is_true (rtype_eqb r r') -> r = r'.

 destruct r; destruct r'.
 unfold rtype_eqb.
 unfold Is_true.
 destruct s; destruct s1; destruct s0; destruct s2; simpl stype_eqb; simpl;
 intuition.
Qed.


Lemma vtype_eqb_implies_rtype_eqb : forall (t t' : vtype),
 Is_true (vtype_eqb t t') -> (rtypeof t) = (rtypeof t').

 destruct t; destruct t'; simpl; unfold Is_true.
 destruct (vtype_eqb t1 t'1 && vtype_eqb t2 t'2); simpl.
 rewrite andb_true_r; apply rtype_eqb_eq.
 rewrite andb_false_r; intuition.
 intuition. intuition. intuition. intuition.
 intuition. intuition.
 destruct (vtype_eqb t1 t'1 && vtype_eqb t2 t'2).
 rewrite andb_true_r; apply rtype_eqb_eq.
 rewrite andb_false_r; intuition.
 intuition. intuition. intuition.
 intuition. intuition. intuition.
 destruct (vtype_eqb t1 t'1 && vtype_eqb t2 t'2).
 rewrite andb_true_r; apply rtype_eqb_eq.
 rewrite andb_false_r; intuition.
 intuition. intuition. intuition. intuition.
 intuition. intuition.
 apply rtype_eqb_eq; intuition.
 intuition. intuition. intuition. intuition. intuition.
 intuition.
 apply rtype_eqb_eq.
 intuition. intuition. intuition.
 intuition. intuition. intuition.
 apply rtype_eqb_eq.
Qed.

Theorem vtype_eqb_refl : forall (t : vtype), Is_true (vtype_eqb t t).

 induction t; simpl; rewrite rtype_eqb_refl;
 try (
  rewrite andb_true_l;
  apply (andb_prop_intro (vtype_eqb t1 t1) (vtype_eqb t2 t2));
  split; assumption; assumption
 ); unfold Is_true; trivial.
Qed.

Lemma vtype_eqb_refl_eq : forall (t : vtype), vtype_eqb t t = true -> t = t.
 intros; reflexivity.
Qed.


Hint Resolve vtype_eqb_implies_rtype_eqb.

Theorem vtype_eqb_eq : forall (t t' : vtype), Is_true (vtype_eqb t t') -> t = t'.

 induction t; simpl vtype_eqb;

 try(
 assert (

  Is_true
   match t' with
    | TSum r' u u' => rtype_eqb r r' && (vtype_eqb t1 u && vtype_eqb t2 u')
    | TProd _ _ _ => false
    | TArrow _ _ _ => false
    | TNum _ => false
    | TBool _ => false
    | TUnit _ => false
   end

   =
   match t' with
    | TSum r' u u' =>
      Is_true (rtype_eqb r r' && (vtype_eqb t1 u && vtype_eqb t2 u'))
    | _ => False
   end

 ) as G;

 destruct t'; reflexivity; rewrite G); destruct t';

 (* assertion proved and used *)

 try(
 intro;
 apply andb_prop_elim in H0; intuition;
 apply andb_prop_elim in H2; intuition;
 apply IHt1 in H0;
 apply IHt2 in H3;
 rewrite H0; rewrite H3;
 apply rtype_eqb_eq in H1; rewrite H1; reflexivity;

 intuition); try (simpl Is_true).

 intuition. intuition. intuition. intuition. intuition.
 intuition. intuition. intuition. intuition. intuition.
 intuition. intuition. intuition. intuition. intuition.
 intuition. intuition. intuition.

 intro. apply rtype_eqb_eq in H0. rewrite H0. reflexivity.

 intuition. intuition. intuition. intuition. intuition.
 intuition.

 intro. apply rtype_eqb_eq in H0. rewrite H0. reflexivity.

 intuition. intuition. intuition. intuition. intuition.
 intuition.

 intro. apply rtype_eqb_eq in H0. rewrite H0. reflexivity.

Qed.

Theorem nat_eq_eq : forall (n m : nat), Is_true (nat_eq n m) -> n = m.

 induction n.
 destruct m.

 trivial.

 simpl nat_eq; unfold Is_true; intuition.

 destruct m.

 simpl nat_eq; unfold Is_true; intuition.

 simpl nat_eq. intro.  apply IHn in H0. elim H0. reflexivity.

Qed.


Theorem var_eq_eq : forall (t : vtype) (x : var t) (x' : var t),
 Is_true (x == x') -> x = x'.

 intros t x x'.
 unfold var_eq. intro G. apply andb_prop_elim in G. elim G. intros I J.
 apply nat_eq_eq in I. apply vtype_eqb_eq in J.
 destruct x. destruct x'. intuition.

Qed.

Theorem var_eq_type_eq : forall (t : vtype) (x x' : var t),
 Is_true (x == x') -> vartype t x = vartype t x'.

 intro t; intros x x';
 unfold var_eq; intro;
 destruct (nat_eq (var_index t x) (var_index t x')).
 rewrite andb_true_l in H0.
 apply vtype_eqb_eq in H0. assumption.

 rewrite andb_false_l in H0; simpl Is_true in H0; elim H0; intuition.

Qed.



(* syntax of SLam terms *)

Section expr.

 Variable var' : vtype -> Set.

 Inductive expr : stype -> vtype -> Set :=
  | Val  : forall (t : vtype) (s : stype), val t -> expr s t

  | Ref  : forall (t : vtype) (s : stype), var' t -> expr s t

  | InjL : forall (t t' : vtype) (s s' : stype) (r : rtype),
           expr s t -> expr s' (TSum r t t')
  | InjR : forall (t t' : vtype) (s s' : stype) (r : rtype),
           expr s t' -> expr s' (TSum r t t')

  | Cross : forall (t t' : vtype) (s s' s'' : stype) (r : rtype),
            expr s t -> expr s' t' -> expr s'' (TProd r t t')

  | Lam : forall (t t' : vtype) (s s' : stype) (r : rtype),
          (var' t -> expr s' t') -> expr s (TArrow r t t')

  | AppL : forall (t t' : vtype) (s s' s'' s''' : stype),
           expr s' (TArrow (L, s'') t t') -> expr s t
           -> expr s''' (t' ** <<t'>>)

  | AppH : forall (t t' : vtype) (s s' s'' : stype),
           expr s' (TArrow (H, s'') t t') -> expr s t
           -> expr H (t' ** <<t'>>)

  | Proj1L : forall (t t' : vtype) (s s' s'' : stype),
             expr s (TProd (L, s') t t')
             -> expr s'' (t ** s')
  | Proj1H : forall (t t' : vtype) (s : stype),
             expr H (TProd (H, s) t t')
             -> expr H (t ** s)
  | Proj2L : forall (t t' : vtype) (s s' s'' : stype),
             expr s (TProd (L, s') t t')
             -> expr s'' (t' ** s')
  | Proj2H : forall (t t' : vtype) (s : stype),
             expr H (TProd (H, s) t t')
             -> expr H (t' ** s)

  | CaseL : forall (t t' t'' : vtype) (s s' s'' : stype) (r : rtype),
            expr L (TSum (L, s'') t t') ->
            (var' t -> expr s' t'') ->
            (var' t -> expr s' t'') ->
            expr s' (t'' ** s'')

  | CaseH : forall (t t' t'' : vtype) (s s' s'' : stype) (r : rtype),
            expr H (TSum (H, s'') t t') ->
            (var' t -> expr s' t'') ->
            (var' t -> expr s' t'') ->
            expr H (t'' ** s'')

 (*
  | Mu : forall (t t' : vtype) (s : stype) (r : rtype),
         var (TArrow r t t')
         -> expr s (TArrow r t t') -> expr s (TArrow r t t')
 *)
 
 with val : vtype -> Set :=
(*
  | Lam : forall (t t' : vtype) (s s' : stype) (r : rtype),
          var t -> expr s' t' -> val (TArrow r t t')
*)
  | Inl : forall (t t' : vtype) (r : rtype), val t -> val (TSum r t t')
  | Inr : forall (t t' : vtype) (r : rtype), val t' -> val (TSum r t t')
  | Pair : forall (t t' : vtype) (r : rtype),
           val t -> val t' -> val (TProd r t t')
  | Num : forall (r : rtype), nat -> val (TNum r)
  | Bol : forall (r : rtype), bool -> val (TBool r)
  | Unit : forall (r : rtype), val (TUnit r).

Check sdot.

Definition protect_val (s : stype) (t : vtype) (v : val t) : val (t ** s) :=

 match v with
  | Inl t t' r v => Inl t t' (sdot r s) v
  | Inr t t' r v => Inr t t' (sdot r s) v
  | Pair t t' r v v' => Pair t t' (sdot r s) v v'
  | Num r n => Num (sdot r s) n
  | Bol r b => Bol (sdot r s) b
  | Unit r => Unit (sdot r s)
 end.

Section protect.


 Definition protect (s s' : stype) (t : vtype) (e : expr s t)
  : expr s (t ** s').

 intros s s' t e.

 refine (

  match e with
   | Val t s v => Val (t ** s') s (protect_val s' t v)
   | Ref t s x => Ref (t ** s') s _
   | InjL t t' s'' s''' r e' => _
   | InjR t t' s'' s''' r e' => _
   | Cross t t' s'' s''' s'''' r e' e'' => _
   | Lam t t' s'' s''' r f => _
   | AppL t t' s'' s''' s'''' s''''' e' e'' => _
   | AppH t t' s'' s''' s'''' e' e'' => _
   | Proj1L t t' s'' s''' s'''' e' => _
   | Proj1H t t' s'' e' => _
   | Proj2L t t' s'' s''' s'''' e' => _
   | Proj2H t t' s'' e' => _
   | CaseL t t' t'' s'' s''' s'''' r e' f f' => _
   | CaseH t t' t'' s'' s''' s'''' r e' f f' => _
  end

 ).

 refine x.

End protect.



Fixpoint val_denote (t : vtype) (v : val t) : vtype_denote t :=

 (* another case where 'match' needs all the extra syntax *)
 match v in (val t) return (vtype_denote t) with
  | Inl t t' _ v => inl (vtype_denote t') (val_denote t v)
  | Inr t t' _ v => inr (vtype_denote t) (val_denote t' v)
  | Pair t t' _ v v' => (val_denote t v, val_denote t' v')
  | Num _ n => n
  | Bol _ b => b
  | Unit _ => tt
 end.

End expr.


Definition expr_denote
 (t : vtype) (s : stype) (e : expr vtype_denote s t) : vtype_denote t.

 intros t s e.

 refine (

 (fix dnote (t : vtype) (s : stype) (e' : expr vtype_denote s t) :=
 
 match e' in (expr _ s t) return (vtype_denote t) with
  | Val _ _ v => val_denote _ _ v
  | Ref _ _ x => x
  | InjL _ _ _ _ _ e' => inl _ (dnote _ _ e')
  | InjR _ _ _ _ _ e' => inr _ (dnote _ _ e')
  | Cross _ _ _ _ _ _ e' e'' => (dnote _ _ e', dnote _ _ e'')
  | Lam _ _ _ _ _ f => fun v => dnote _ _ (f v)
  | AppL _ _ _ _ _ _ e' e'' => _
  | AppH _ _ _ _ _ e' e'' => _
  | Proj1L _ _ _ _ _ e' => _
  | Proj2L _ _ _ _ _ e' => _
  | Proj1H  _ _ _ e' => _
  | Proj2H  _ _ _ e' => _

  | CaseL t' t'' t''' _ _ _ _ e' f f' =>
    match (dnote _ _ e') return (vtype_denote _) with    
     | inl x => dnote _ _ _
     | inr x => dnote _ _ _ 
    end

  | CaseH _ _ _ _ _ _ _ e' f f' =>
    match (dnote _ _ e') with
     | inl x => _
     | inr x => _
    end

 end) t s e

 ). (* end refine *)

 (* AppL *)
 rewrite <- (vtype_annot_erase t').
 exact ((dnote _ _ e'0) (dnote _ _ e'')).

 (* AppH *)
 rewrite <- (vtype_annot_erase t').
 exact ((dnote _ _ e'0) (dnote _ _ e'')).

 (* Proj1L *)
 rewrite <- (vtype_annot_erase t1).
 exact (fst (dnote _ _ e'0)).

 (* Proj1H *)
 rewrite <- (vtype_annot_erase t1).
 exact (fst (dnote _ _ e'0)).

 (* Proj1L *) 
 rewrite <- (vtype_annot_erase t').
 exact (snd (dnote _ _ e'0)).

 (* Proj2L *)
 rewrite <- (vtype_annot_erase t').
 exact (snd (dnote _ _ e'0)).

 (* CaseL *)
 trivial.
 refine (f x).
 rewrite (vtype_annot_erase t' s'') in f.
 apply vtype_annot_erase in f.
 exact (dnote _ _ (f x)).

 rewrite <- (vtype_annot_erase  t'').

 refine (dnote _ _ _).

  




Definition substitute
  (s : stype) (t : vtype) (x : var t) (v : val t) (e : expr s t) :
   expr s t.

 intros s t x v e.

 refine (

  (fix sbst (s : stype) (t : vtype) (e : expr s t) :=

  match e with
   | Val t' s' v => Val s' v
   | Ref t' s' x' => if var_eq_dec x x' then Val s' _ else Ref s' x'
   | InjL t' _ s' _ r e' => InjL _ _ r (sbst s' t' e')
   | InjR _ t' s' _ r e' => InjR _ _ r (sbst s' t' e')

   | Cross t' t'' s' s'' s''' r e' e'' =>
     Cross s''' r (sbst s' t' e') (sbst s'' t'' e'')

   | Lam t' t'' s' s'' r x' e' =>
     if var_eq_dec x x' then Lam s' r x' e'
     else Lam s' r x' (sbst s'' t'' e')

   | Proj1L t' t'' s' s'' s''' e' => Proj1L s''' (sbst _ _ e')
   | Proj2L t' t'' s' s'' s''' e' => Proj2L s''' (sbst _ _ e')

   | Proj1H t' t'' s' e' => Proj1H (sbst _ _ e')
   | Proj2H t' t'' s' e' => Proj2H (sbst _ _ e')

   | AppL t' t'' s' s'' s''' s'''' e' e'' =>
     AppL s'''' (sbst s'' _ e') (sbst s' _ e'')

   | AppH t' t'' s' s'' s''' e' e'' =>
     AppH (sbst _ _ e') (sbst s' _ e'')

   | CaseL t' t'' t''' s' s'' s''' r e' x' e'' e''' =>
     if var_eq_dec x x' then CaseL s''' r e' x' e'' e'''
     else CaseL s''' r e' x' (sbst _ _ e'') (sbst _ _ e''')

   | CaseH t' t'' t''' s' s'' s''' r e' x' e'' e''' =>
     if var_eq_dec x x' then CaseH s''' r e' x' e'' e'''
     else CaseH s''' r e' x' (sbst _ _ e'') (sbst _ _ e''')

   | Mu t' t'' s' r x' e' =>
     if var_eq_dec x x' then Mu x' e'
     else Mu x' (sbst _ _ e')

  end) s t e

 ).

 assert (t = t').
 apply vtype_eqb_eq. unfold var_eq in _H. apply andb_prop_elim in _H.
 elim _H. intros. destruct x. destruct x'. simpl vartype in H1.
 exact H1.

 rewrite H0 in v.
 exact v.

Defined.


Definition lam_test
 (s : stype) (t : vtype) (x : var t) (e : expr s t) :
 option (expr s t) :=

 match e with
  | Lam _ _ _ _ _ x e' => Some (fun (v : vtype_denote t) => substitute x v e')
  | _ => None
 end.



Check (inr bool 0).
Check (inl nat false).




(* environment of variable bindings *)
Inductive env : Set :=
 | Empty : env
 | Bind : forall (t : vtype), var t -> val t -> env -> env.


Notation "x :== v ::: rho" := (Bind x v rho) (right associativity, at level 60).

Check (Var (TNum (H, H)) 0).

Check
(let x := Var (TNum (H, H)) 0 in
 let v := Num (H, H) 1 in
 (x :== v ::: Empty)).

(* extend the environment with a new variable binding *)
Definition ext (t : vtype) :
 forall (x : var t) (v : val t), env -> env  :=
  fun (x : var t) (v : val t) (rho : env) => Bind x v rho.

Notation "<< rho [ x |-> v ] >>" := (ext x v rho)
 (right associativity, at level 60).



Fixpoint bound (t : vtype) (x : var t) (rho : env) : Prop :=
 match rho with
  | Bind _ x' _ rho' => if x == x' then True else bound x rho'
  | Empty => False
 end.

Fixpoint notbound (t : vtype) (x : var t) (rho : env) : Prop :=
 match rho with
  | Bind _ x' _ rho' => if x == x' then False else notbound x rho'
  | Empty => True
 end.

Definition bound_dec : forall (t : vtype) (x : var t) (rho : env),
 {bound x rho} + {~bound x rho}.

 intros t.
 inversion x.
 induction rho.
 
 refine (right _ _). unfold bound. intuition.

 unfold bound; destruct (x == v). refine (left _ _). trivial.
 apply IHrho.
Defined.

Lemma bound_ext : forall (t : vtype) (x x' : var t) (v : val t) (rho : env),
 bound x rho -> bound x (x' :== v ::: rho).

 intros t x x' v.
 induction rho.
 simpl bound. intuition.

 simpl bound. destruct (x == v0). destruct (x == x'). intuition. intuition.

 intro G. destruct (x == x'). trivial. exact G.

Qed.

Lemma bound_ext_alt : forall (t : vtype) (x x' : var t) (v : val t) (rho : env),
 bound x (x' :== v ::: rho) -> x = x' \/ bound x rho.

 intros t x x' v.
 induction rho.

 unfold bound. intro G. apply var_eq_eq in G. left. exact G.

 intro G. elim IHrho.
 
 intuition.

 intro J.
 simpl bound. right. destruct (x == v0). trivial. exact J.

 simpl bound. destruct (x == x'). trivial.


 apply (bound_ext x (x' :== v ::: v0 :== v1 ::: rho)) in G.


Theorem bound_ext_var :
 forall (t : vtype) (x x' : var t) (v : val t) (rho : env),
 ~bound x rho /\ bound x (x' :== v ::: rho) -> x = x'.

 intros t x x' v rho.

 inversion 1. 

 unfold bound; destruct (x == x'); simpl bound.
 


Definition lkp : forall (t : vtype) (x : var t) (rho : env), option (val t).

 intros t x rho.

 refine (

  (fix lkp' (rho' : env) {struct rho'} :=
   match rho' with
    | Bind z x' v rho'' => if var_eq_dec x x' then Some _ else lkp' rho''
    | Empty => None
   end) rho

 ). clear lkp'. (* for reasons that are obscure, 'clear' is necessary here *)


 (* show that x and x' must have the same type if == *)
 assert (z = t).
 unfold var_eq in _H. apply andb_prop_elim in _H. elim _H; intros.
 apply vtype_eqb_eq in H1.  apply nat_eq_eq in H0. destruct x. destruct x'.
 simpl vartype in H1.
 symmetry. exact H1.

 (* which then makes the straightforward definition well-typed *)
 rewrite H0 in v.
 exact v.

Defined.

Inductive lkpto : forall (t : vtype), env -> var t -> val t -> Prop :=
 | Lkp : forall (t : vtype) (rho : env) (x : var t) (v : val t),
         lkp x rho = Some v -> lkpto rho x v.

Notation "x |->[ rho ] v" := (lkpto rho x v) (no associativity, at level 90).


Check (Var (TUnit (L, L)) 0).
Check (Unit (L, L)).

Check lkp.
Check (
 let x := Var (TUnit (L, L)) 0 in
 let x' := x in
 let v := Unit (L, L) in
 lkp x (x' :== v ::: Empty)

).

Check lkp.

Reserved Notation "e ==>[ rho ] e'" (no associativity, at level 90).


Definition deref (t : vtype) (x : var t) (rho : env) :
 (val t) + {notbound x rho}.

 intros t x rho.

 refine (

  match lkp x rho with
   | Some v => _
   | None => _
  end
 ).

 refine (inleft _ _). exact v.

 refine (inright _ _).
 induction rho.
 inversion x.
 constructor.
 unfold notbound.
 apply IHrho.
 destruct (x == v). 
 
 



Fixpoint exp_denote
 (t : vtype) (s : stype) (e : expr s t) (rho : env) : vtype_denote t :=

 match e with
  | Val t _ v => val_denote v rho
  | Ref t _ x => val_denote (lkp x rho)
  | _ => None
 end
with val_denote (t : vtype) (e : val t) (rho : env) : vtype_denote t :=
 match e with
  | Inl t t' _ v => inl (vtype_denote t') (val_denote _ v)
  | Inr t t' _ v => inr (vtype_denote t) (val_denote _ v)
  | Pair t t' _ v v' => (val_denote v, val_denote v')
  | Num _ n => n
  | Bol _ b => b
  | Unit _ => tt
 end.



(* everything up to here is current 2011.05.05 *)


Inductive op_red (rho : env) : forall (s s' : stype) (t t' : vtype),
 expr s t -> expr s' t' -> Prop :=

 | DeRef : forall (t : vtype) (v : val _) (x : var t) (s : stype),
   (x |->[rho] v) -> (Ref s x) ==>[rho] (Val s v)

 | Beta : forall (t t' : stype) (s s' : stype), (v : val _) (e : expr s t),
   (x |->[rho] v) App (Val s (Lam x e)) v

where "e ==>[ rho ] e'" := (op_red rho e e').

Definition op_red
 (s : stype) (t : vtype) : expr s t -> env -> (expr s t) * env


 intros s t e rho.

 refine (
  
  match e return (expr s t) * env with
   | Val _ _ _ => (e, rho)

   | Ref t' _ x =>
     match lkp x rho with
      | Some v => if vtype_eqb_dec t t' then (_, rho) else (Val s (Wrong t), rho)
      | None => (Val s (Wrong t), rho)
     end

   | Proj1L t _ _ _ _ (Val t'' _ (Pair _ _ _ z _)) =>
     if vtype_eqb_dec t t'' then (Val _ _, rho) else _

   | Proj2L t t' _ _ _ (Val t'' _ (Pair _ _ _ _ v')) => (Val _ _, rho)
   | _ => (e, rho)
  end
 ).

 (* Ref case *)
 assert (t = t').
 apply vtype_eqb_eq in _H. exact _H. (* and that's it *)
 rewrite <- H0 in v. exact (Val s v).

 (* Proj1L case *)
 assert (t = t1).
 apply vtype_eqb_eq in _H. rewrite <- _H in v.
 destruct e0.

 

 simpl vtype_eqb in _H. simpl Is_true in _H.
 elim _H. intuition.

Defined.





(* everything up to here is current;
   code after this point is to-be-updated *)

(* reduction stepping function of the base operational semantics *)
Definition op_red
(e : expr) (rho : env) : (expr * env) :=
 match e with
  | Var x => (Val (rho x) (sgm x), (rho, sgm))

  | App (Lam x s t k) (Val v k') s' =>
    if slow (fr k) s' then
     let rho' := ext rho x v in
     let sgm' := setvl sgm x s in
      (Protect (fir k) t, (rho', sgm'))
    else (Wrong, (rho, sgm))

  | ProjL (Val (Pair v _) k) s' =>
    if slow (fr k) s' then
     (Protect (fir k) (Val v k), (rho, sgm))
    else (Wrong, (rho, sgm))

  | ProjR (Val (Pair v _) k) s' =>
    if slow (fr k) s' then
     (Protect (fir k) (Val v k), (rho, sgm))
    else (Wrong, (rho, sgm))

  | Case (Val (Inl v) k) x _ e _ s =>
    if slow (fr k) s then
     let rho' := ext rho x v in
     (Protect (fir k) e, (rho', sgm))
    else (Wrong, (rho, sgm))

  | Case (Val (Inr v) k) x _ _ e s =>
    if slow (fr k) s then
     let rho' := ext rho x v in
     (Protect (fir k) e, (rho', sgm))
    else (Wrong, (rho, sgm))

  | Protect s (Val v k) => (Val v (dot s k), (rho, sgm))

  | Prod (Val v k) (Val v' k') s => (Val (Pair v v') k, (rho, sgm))

  | _ => (Wrong, (rho, sgm))
 end.


(* a function recognizing the presence of an opsem premise pattern *)
Definition op_red_match (e : expr) : bool :=
 match e with
  | Var _ => true

  | App (Lam _ _ _ _) (Val _ _) _ => true

  | ProjL (Val (Pair _ _) _) _ => true

  | ProjR (Val (Pair _ _) _) _ => true

  | Case (Val (Inl _) _) _ _ _ _ _ => true

  | Case (Val (Inr _) _) _ _ _ _ _ => true

  | Protect _ (Val _ _) => true

  | Prod (Val _ _) (Val _ _) _ => true

  | _ => false
 end.


(* structuring of evaluation in a left-to-right manner *)
Fixpoint eval_red (e : expr) (rho : env) (sgm : acp) : expr :=
 if op_red_match e then fst (op_red e rho sgm) else
 match e with
  | App (Lam x s t k) t' s' => App (Lam x s t k) (eval_red t' rho sgm) s'
  | App t t' s => App (eval_red t rho sgm) t' s
  | ProjL t s => ProjL (eval_red t rho sgm) s
  | ProjR t s => ProjR (eval_red t rho sgm) s
  | InjL t k => InjL (eval_red t rho sgm) k
  | InjR t k => InjR (eval_red t rho sgm) k
  | Prod (Val v k) t' k' => Prod (Val v k) (eval_red t' rho sgm) k'
  | Prod t t' k' => Prod (eval_red t rho sgm) t' k'
  | Protect s t => Protect s (eval_red t rho sgm)
  | Case t x k t' t'' s => Case (eval_red t rho sgm) x k t' t'' s
  | Lam x s t k => Lam x s t k
  | Val v k => Val v k
  | _ => Wrong
 end.


(* get the reader type of an expression *)
Fixpoint sreader (e : expr) (sgm : acp) : stype :=
 match e with
  | Val _ (r, _) => r
  | Var x => fr (sgm x)
  | InjL e (r, _) => r
  | InjR e (r, _) => r
  | Prod _ _ (r, _) => r
  | Lam _ _ _ (r, _) => r
  | App _ _ r => r
  | ProjL _ r => r
  | ProjR _ r => r
  | Protect s e => lub s (sreader e sgm)
  | Case _ _ _ _ _ r => r
  | _ => L
 end.

(* checking of the security type annotations *)

Fixpoint swelltyped (e : expr) (sgm : acp) : Prop :=
 match e with
  | Val _ _ => True
  | Var _ => True
  | InjL t _ => swelltyped t sgm
  | InjR t _ => swelltyped t sgm
  | Lam x k t _ => swelltyped t (setvl sgm x k)
  | App t t' r => (pslow (sreader t sgm) r) /\ swelltyped t' sgm
  | Prod t t' _ => swelltyped t sgm /\ swelltyped t' sgm
  | ProjL t r => (pslow (sreader t sgm) r) /\ swelltyped t sgm
  | ProjR t r => (pslow (sreader t sgm) r) /\ swelltyped t sgm
  | Protect s t => swelltyped t sgm
  | Case t x k t' t'' r =>
    let sgm' := setvl sgm x k in
    (pslow (sreader t sgm) r) /\ swelltyped t' sgm' /\ swelltyped t'' sgm'
  | _ => False
 end.

Definition initsgm : acp := fun x => (L, L).

Definition ex1 : Prop :=
 swelltyped (ProjR (Prod (Val Unit (H, H)) (Val Unit (L, L)) (H, H)) L) initsgm.

Eval compute in ex1.

Definition ex2 : Prop :=
 swelltyped
  (Case (Val (Inr Unit) (H, H)) 0 (H, H)
   (Val (Num 1) (L, L)) (Val (Num 2) (L, L)) L) initsgm.

Eval compute in ex2.

(* some useful predicates *)

Inductive valuex : expr -> Prop :=
 | value : forall (v : val) (k : ftype), valuex (Val v k).

Inductive destructor : expr -> Prop :=
 | appdest : forall (e e' : expr) (s : stype), destructor (App e e' s)
 | projldest : forall (e : expr) (s : stype), destructor (ProjL e s)
 | projrdest : forall (e : expr) (s : stype), destructor (ProjR e s)
 | casedest : forall (e e' e'' : expr) (x : var) (s : stype),
                destructor (Case e x e' e'' s).

(* this is the end of the file *)


(* old theorems from above *)

