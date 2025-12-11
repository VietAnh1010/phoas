Record state (S A : Type) : Type := State { run_state : S -> A * S }.

Arguments State {S A} _.
Arguments run_state {S A} _ _.

Definition pure {S A} (x : A) : state S A :=
  State (fun s => (x, s)).

Definition map {S A B} (f : A -> B) (m : state S A) : state S B :=
  State (fun s => let (x, s) := run_state m s in (f x, s)).

Definition app {S A B} (m1 : state S (A -> B)) (m2 : state S A) : state S B :=
  State (fun s => let (f, s) := run_state m1 s in let (x, s) := run_state m2 s in (f x, s)).

Definition bind {S A B} (m : state S A) (f : A -> state S B) : state S B :=
  State (fun s => let (x, s) := run_state m s in run_state (f x) s).

Definition get {S} : state S S :=
  State (fun s => (s, s)).

Definition put {S} (s : S) : state S unit :=
  State (fun _ => (tt, s)).

Definition gets {S A} (f : S -> A) : state S A :=
  State (fun s => (f s, s)).

Definition modify {S} (f : S -> S) : state S unit :=
  State (fun s => (tt, f s)).
