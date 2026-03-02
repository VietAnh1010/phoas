From Stdlib Require Import List String ZArith.
From shift_reset.lib Require sum.
From shift_reset.core Require Import syntax syntax_notation.
From shift_reset.interpreter Require Import interpreter error.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope term_scope.

Definition range (s e : Z) : list Z :=
  let fix go s l :=
    match l with
    | O => []
    | S l' => s :: go (s + 1) l'
    end
  in
  go s (Z.to_nat (e - s)).

Fixpoint int_list_to_val_term (xs : list Z) : val_term :=
  match xs with
  | [] => <{ Inl () }>
  | x :: xs' => <{ Inr ({TVInt x}, {int_list_to_val_term xs'}) }>
  end.

Fixpoint val_to_int_list (v : val) : exn + list Z :=
  match v with
  | VInl VTt => inr []
  | VInr (VPair (VInt x) v') => sum.map (cons x) (val_to_int_list v')
  | _ => inl (Failure "val_to_int_list")
  end.

Definition eval_term_to_int_list (fuel : nat) (t : term) : exn + list Z :=
  sum.bind (eval_term fuel t) val_to_int_list.
