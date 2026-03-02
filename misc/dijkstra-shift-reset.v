Require Import List.
Import ListNotations.

Definition DSR (A B C : Type) :=
  (A -> (B -> Prop) -> Prop) -> (C -> Prop) -> Prop.

Definition pure {A B : Type} (x : A) : DSR A B B :=
  fun k post => k x post.

Definition bind {A B C D E : Type} (m : DSR A D E) (f : A -> DSR B C D) : DSR B C E :=
  fun k post => m (fun a => f a k) post.

Definition shift {T A B C : Type} (f : (forall (D : Type), T -> DSR A D D) -> DSR C C B) :=
  fun k post => f (fun D t k' post' => k t (fun a => k' a post')) (fun c post' => post' c) post.

Definition reset {T A B : Type} (m : DSR A A T) : DSR T B B :=
  fun k post => m (fun a post' => post' a) (fun t => k t post).

Definition run_DSR {A : Type} (m : DSR A A A) (post : A -> Prop) : Prop :=
  m (fun a post' => post' a) post.

Example dsr1 {A : Type} : DSR nat A A :=
  reset (shift (fun k => k _ 1)).

Example dsr2 {A : Type} : DSR nat A A :=
  bind dsr1 (fun n => bind dsr1 (fun m => pure (n + m))).

Fixpoint dsr3 (xs : list nat) :=
  match xs with
  | [] => shift (fun k => k (list nat) [])
  | x :: xs' => bind (dsr3 xs') (fun r => pure (x :: r))
  end.

Compute (run_DSR (reset (dsr3 [1; 2; 3; 4; 5; 6; 7; 8; 9; 10])) (fun b => 0 <= length b)).
