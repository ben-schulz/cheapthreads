(*

  this is ~/cheapthreads/CTC/CT-1.0/RPSLam/Mechanization/Maybe.v

  a formalization of the 'Maybe' monad

  put here 2011.05.24

  Schulz

*)

Require Import FunctionalExtensionality.

Module Maybe.

Inductive Maybe (a : Type) : Type :=
 | Nothing : Maybe a
 | Just : a -> Maybe a.

Definition eta_maybe (a : Type) (x : a) : Maybe a := Just a x.

Notation "## v" := (eta_maybe _ v) (no associativity, at level 10).

Definition bind_maybe (a b : Type) (x : Maybe a) (f : a -> Maybe b) : Maybe b :=
 match x with
  | Nothing => Nothing _
  | Just y => f y
 end.

Notation "x >>= f" := (bind_maybe _ _ x f) (left associativity, at level 20).

Theorem maybe_unit_l : forall (a b : Type) (x : a) (f : a -> Maybe b),
 (## x) >>= f = f x.

 intros a b x f; unfold eta_maybe; unfold bind_maybe; reflexivity.
Qed.

Theorem maybe_unit_r : forall (a : Type) (x : Maybe a),
 (x >>= fun v => ## v) = x.

 intros a x; unfold eta_maybe; unfold bind_maybe; destruct x; reflexivity.
Qed.

Theorem maybe_bind_assoc :
 forall (a b c : Type) (x : Maybe a) (f : a -> Maybe b) (g : b -> Maybe c),
  x >>= (fun v => f v >>= g) = (x >>= f) >>= g.

 intros a b c x f g; unfold bind_maybe; destruct x.
 reflexivity.
 destruct (f a0); reflexivity.
Qed.


End Maybe.