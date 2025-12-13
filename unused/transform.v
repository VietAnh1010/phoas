(*
From shift_reset.lib Require Import monad.

Class Transform (M N : Type -> Type) : Type :=
  transform : forall {A}, M A -> N A.

Class Lift (M : Type -> Type) (T : (Type -> Type) -> Type -> Type) : Type :=
  lift : forall {A}, M A -> T M A.

Instance Lift_reader_t R M : Lift M (reader_t R) :=
  fun A m => ReaderT (fun _ => m).

Instance Lift_state_t S M `{MonadMap M} : Lift M (state_t S) :=
  fun A m => StateT (fun s => monad_map (fun x => (x, s)) m).

Instance Lift_except_t E M `{MonadMap M} : Lift M (except_t E) :=
  fun A m => ExceptT (monad_map inr m).

Class Hoist (M N : Type -> Type) (T : (Type -> Type) -> Type -> Type) : Type :=
  hoist : forall {A}, T M A -> T N A.

Instance Hoist_reader_t R M N `{Transform M N} : Hoist M N (reader_t R) :=
  fun A m => ReaderT (fun r => transform (run_reader_t m r)).

Instance Hoist_except_t E M N `{Transform M N} : Hoist M N (except_t E) :=
  fun A m => ExceptT (transform (run_except_t m)).

Instance Hoist_state_t S M N `{Transform M N} : Hoist M N (state_t S) :=
  fun A m => StateT (fun s => transform (run_state_t m s)).

(*
Instance Transform_identity_reader R : Transform identity (reader R) :=
  fun A m => ReaderT (fun _ => m).

Instance Transform_identity_except E : Transform identity (except E) :=
  fun A m => ExceptT (Identity (inr (run_identity m))).

Instance Transform_identity_state S : Transform identity (state S) :=
  fun A m => StateT (fun s => Identity (run_identity m, s)).

Instance Transform_reader_reader_t R M `{Transform identity M} : Transform (reader R) (reader_t R M) :=
  fun A m => ReaderT (fun r => transform (run_reader_t m r)).

Instance Transform_except_except_t E M `{Transform identity M} : Transform (except E) (except_t E M) :=
  fun A m => ExceptT (transform (run_except_t m)).

Instance Transform_state_state_t S M `{Transform identity M} : Transform (state S) (state_t S M) :=
  fun A m => StateT (fun s => transform (run_state_t m s)).
*)

Instance Transform_Lift : forall M T `{Lift M T}, Transform M (T M) :=
  @lift.

Instance Transform_Transform_Lift M N T `{Transform M N} `{Lift N T} : Transform M (T N) :=
  fun A m => lift (transform m).

Instance Transform_Hoist : forall M N T `{Hoist M N T}, Transform (T M) (T N) :=
  @hoist.

From Stdlib Require Import Extraction.

Lemma foo : identity nat -> reader nat nat.
Proof. apply transform. Show Proof. Defined.
*)
