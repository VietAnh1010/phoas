From Stdlib Require Import List.
Import ListNotations.

Fixpoint assoc {A B} (A_eqb : A -> A -> bool) (k : A) (ps : list (A * B)) : option B :=
  match ps with
  | [] => None
  | (k', v) :: ps' => if A_eqb k k' then Some v else assoc A_eqb k ps'
  end.
