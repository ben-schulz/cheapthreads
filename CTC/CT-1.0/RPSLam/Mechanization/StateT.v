(*

 this is ~/cheapthreads/CTC/CT-1.0/RPSLam/Mechanization/StateT.v

 a definition of the state monad and state monad transformer,
 together with a proof of the monad laws and some other useful properties

 put here 2011.05.11

 Schulz

*)


Module StateT.

Require Import FunctionalExtensionality.


Definition State (s : Type) (a : Type) : Type := s -> a * s.

Definition eta_st (s : Type) (a : Type) (v : a) : State s a :=
 fun (x : s) => (v, x).


Notation "## v" := (eta_st _ _ v) (no associativity, at level 10).

Definition bind_st (s : Type) (a b : Type) (m : State s a) (f : a -> State s b) :
 State s b :=

 fun (x : s) => let (v, x') := (m x) in (f v) x'.

Notation "x >>=_st f" := (bind_st _ _ _ x f) (left associativity, at level 20).
Notation "x >>_st m" := (bind_st _ _ _ x (fun _ => m))
 (left associativity, at level 20).


(* a non-standard operation on state that I'm trying out *)


(* the monad laws *)

Theorem unit_l_st : forall (s a b : Type) (f : a -> State s b) (v : a),
 (## v >>=_st f) = (f v).

 intros s a b f v.
 unfold bind_st; unfold eta_st; symmetry; apply eta_expansion.
Qed.

Theorem unit_r_st : forall (s a : Type) (m : State s a) (v : a),
 m >>=_st (fun x => ##x) = m.

 intros s a m v.
 unfold eta_st; unfold bind_st. rewrite eta_expansion.
 apply functional_extensionality. intro x. destruct (m x).
 reflexivity.
Qed.

Theorem bind_assoc_st :
 forall (s a b c : Type) (m : State s a)
        (f : a -> State s b) (g : b -> State s c),
 ((m >>=_st f) >>=_st g) = (m >>=_st (fun x => (f x) >>=_st g)).

 intros s a b c m f g.

 unfold bind_st. apply functional_extensionality. intro x.
 destruct (m x). reflexivity.
Qed.

(*
  and that's all the monad laws, proving that this is in fact the state monad
 *) 


(* the standard morphisms: *)
Definition upd (s : Type) (f : s -> s) : State s unit := fun x => (tt, f x).
Definition get (s : Type) : State s s := fun x => (x, x).
Definition put (s : Type) (v : s) := upd s (fun _ => v).

Implicit Arguments upd [s].

Implicit Arguments put [s].

(* proof of the state monad axioms as in [Harrison, Hook 2005] *)

Theorem st_seq : forall (s : Type) (f f' : s -> s),
 (upd f >>_st upd f') = upd (fun x => f' (f x)).

 intros s f f'; apply eta_expansion.
Qed.

Theorem st_canc : forall (s : Type) (f : s -> s),
 ((get s) >>_st (upd f)) = upd f.

 intros s f; unfold bind_st. simpl. apply eta_expansion.
Qed.

(* some useful theorems specific to State: *)

Theorem put_canc : forall (s : Type) (v v' : s), put v >>_st put v' = put v'.

 intros s v v'.
 unfold put. apply st_seq. 
Qed.

Theorem put_get : forall (s : Type) (v : s),
 (put v >>_st (get s)) = (put v >>_st ##v).

 intros s v. apply eta_expansion.
Qed.


(* and a State-monad-specific monad transformer *)

Definition liftstst (s s' : Type) :=

 fun (a : Type) (m : State s a) =>
  fun (x : s') =>  m >>=_st (fun (v : a) => ## (v, x)).

Implicit Arguments liftstst [a].


Check liftstst.

(*
  you can easily verify that the above is the correct type, i.e. matches
  the result of applying of apply 'liftSt' to the state monad:

  State s a = s -> (a, s)

  StateT s m a = s -> m (a, s)

  liftSt :: m a -> StateT s m a

  ==> State s a -> StateT s' (State s) a
  ==> State s a -> (s' -> State s (a, s'))

  which matches the above.

*)


(* a two-level state monad *)

Section SepState.

 Definition SepState (s s' : Type) (a : Type) : Type := s' -> State s (a * s').

 Definition eta_sep (s s' a : Type) (v : a) : SepState s s' a :=
  fun (x : s') => fun (y : s) => (v, x, y).

 Definition bind_sep (s s' a b : Type)
  (m : SepState s s' a) (f : a -> SepState s s' b) : SepState s s' b :=

  fun (x : s') => fun (y : s) =>
   let (s'', y') := m x y in
   let (v, x') := s'' in (f v) x' y'.


 Notation "### x" := (eta_sep _ _ _ x) (no associativity, at level 10).

 Notation "x >>=_sep f" := (bind_sep _ _ _ _ x f)
  (left associativity, at level 20).

 Notation "x >>_sep y" := (bind_sep _ _ _ _ x (fun _ => y))
  (left associativity, at level 20).

(* proof of the monad laws in the lifted monad *)

 Theorem unit_l_sep :
  forall (s s' a b : Type) (f : a -> SepState s s' b) (x : a),
   ###x >>=_sep f = f x.

  intros s s' a b f x.
  unfold bind_sep; unfold eta_sep.
  apply functional_extensionality; intro x0.
  apply functional_extensionality; intro y.
  reflexivity.
 Qed.

 Theorem unit_r_sep :
  forall (s s' a : Type) (m : SepState s s' a),
   m >>=_sep (fun (v : a) => ###v) = m.

 intros s s' a m.
 unfold bind_sep; unfold eta_sep.
 apply functional_extensionality; intro x.
 apply functional_extensionality; intro y.
 destruct (m x y). destruct p.
 reflexivity.
Qed.

 Theorem bind_assoc_sep :
  forall (s s' a b c : Type) (m : SepState s s' a)
         (f : a -> SepState s s' b) (g : b -> SepState s s' c),
  m >>=_sep (fun (x : a) => (f x) >>=_sep g) =
   (m >>=_sep f) >>=_sep g.

 intros s s' a b c m f g.
 unfold bind_sep.
 apply functional_extensionality; intro x.
 apply functional_extensionality; intro y.
 destruct (m x y). destruct p.
 reflexivity.
Qed.
         

(* show that (in this case) lifting distributes over bind *)
 Theorem lift_bind_dist :
  forall (s s' a b : Type) (m : State s a) (f : a -> State s b),
   liftstst s s' (m >>=_st f) =
    (liftstst s s' m) >>=_sep (fun x => liftstst s s' (f x)).

 intros s s' a b m f.
 unfold bind_st; unfold bind_sep; unfold liftstst.
 apply functional_extensionality; intro x.
 apply functional_extensionality; intro x0.
 compute. destruct (m x0). reflexivity.
Qed.


 Definition get_L (s s' : Type) : SepState s s' s :=
  fun (x : s') => fun (y : s) => (y, x, y).

 Definition get_R (s s' : Type) : SepState s s' s' :=
  fun (x : s') => fun (y : s) => (x, x, y).

 Definition upd_L (s s' : Type) (f : s -> s) : SepState s s' unit :=
  fun (x : s') => fun (y : s) => (tt, x, f y).

 Definition upd_R (s s' : Type) (f : s' -> s') : SepState s s' unit :=
  fun (x : s') => fun (y : s) => (tt, f x, y).

 Definition put_L (s s' : Type) (v : s) : SepState s s' unit :=
  upd_L s s' (fun (_ : s) => v).

 Definition put_R (s s' : Type) (v : s') : SepState s s' unit :=
  upd_R s s' (fun (_ : s') => v).


Check st_canc.

(* proof that the state axioms are satisfied *)

 Theorem sep_canc_l :
  forall (s s' : Type) (f : s -> s),
   get_L s s' >>_sep upd_L s s' f = upd_L s s' f.

 intros s s' f.
 unfold bind_st; compute.
 reflexivity.
Qed.

 Theorem sep_canc_r :
  forall (s s' : Type) (f : s' -> s'),
   get_R s s' >>_sep upd_R s s' f = upd_R s s' f.

 intros s s' f.
 unfold bind_st; compute.
 reflexivity.
Qed.

 Theorem sep_seq_r :
  forall (s s' : Type) (f f' : s -> s),
   upd_L s s' f >>_sep upd_L s s' f' = upd_L s s' (fun (x : s) => f' (f x)).

 intros s s' f f'.
 unfold bind_sep; compute.
 reflexivity.
Qed.

 Theorem sep_seq_l :
  forall (s s' : Type) (f f' : s' -> s'),
   upd_R s s' f >>_sep upd_R s s' f' = upd_R s s' (fun (x : s') => f' (f x)).

 intros s s' f f'.
 unfold bind_sep; compute.
 reflexivity.
Qed.



(* proof of non-interference between state actions *)

 Definition st_nonint
  (s s' a : Type) (m : SepState s s' a) (m' : SepState s s' a) : Prop :=

  m >>_sep m' = m' >>_sep m.

 Notation "m #= n" := (st_nonint _ _ _ m n) (left associativity, at level 50).

 Theorem upd_nonint : forall (s s' : Type) (f : s -> s) (f' : s' -> s'),
  upd_L s s' f #= upd_R s s' f'.

 intros s s' f f'. unfold st_nonint; unfold bind_sep. reflexivity.
Qed.

 Theorem lift_nonint : forall (s s' : Type) (f : s -> s) (f' : s' -> s'),
  liftstst s s' (upd f) #= upd_R s s' f'.

 intros s s' f f'.
 unfold liftstst; unfold st_nonint. compute.
 reflexivity.
Qed.

End SepState.

End StateT.


(* THIS IS THE END OF THE FILE *)


