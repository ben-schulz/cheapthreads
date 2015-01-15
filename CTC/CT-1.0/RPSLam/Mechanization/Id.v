(*
  this is ~/cheapthreads/CTC/CT-1.0/RPSLam/Mechanization/Id.v

  a formalization of the identity monad

  while this is a rather trivial thing to formalize, I'm using it as a
  stepping-stone to developing monadic stype interpreter semantics that
  are compatible with Coq

  put here 2011.05.19

  Schulz

*)

Module Id.

Definition Id (a : Set) := a.

Definition eta_id (a : Set) := fun (x : a) => x.

Definition bind_id (a b : Set) (x : a) (f : a -> Id b) := f x.

Notation "x >>= f" := (bind_id _ _ x f) (no associativity, at level 20).

Notation "## x" := (eta_id _ x) (no associativity, at level 10).

(* prove the monad laws *)
Theorem id_unit_l : forall (a b : Set) (x : a) (f : a -> Id b),
  (## x) >>= f = f x.

 intros a b x f.
 unfold eta_id; unfold bind_id; reflexivity.
Qed.

Theorem id_unit_r : forall (a : Set) (x : Id a), (x >>= fun v => ## v) = x.

 intros a x.
 unfold bind_id; unfold eta_id; reflexivity.
Qed.

Theorem id_bind_assoc :
 forall (a b c : Set) (x : Id a) (f : a -> Id b) (g : b -> Id c),
  x >>= f >>= (fun v => g v) = x >>= (fun v => (f v >>= g)).

 intros a b c x f g.
 unfold bind_id; reflexivity.
Qed.

(* oh look, everything is obvious.  As it should be. *)

End Id.