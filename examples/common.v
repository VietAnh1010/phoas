From Stdlib Require Import List String ZArith.
From shift_reset.lib Require Import sum.
From shift_reset.core Require Import syntax syntax_notation val.
From shift_reset.interpreter Require Import interpreter error.
Import ListNotations SumNotations.

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

Fixpoint list_to_expr {A} (f : A -> expr) (xs : list A) : expr :=
  match xs with
  | [] => <{ [] }>
  | x :: xs' => <{ {f x} :: {list_to_expr f xs'} }>
  end.

Definition list_int_to_expr : list Z -> expr :=
  list_to_expr EInt.

Definition val_to_list_int : val -> option (list Z) :=
  val_to_list_of val_to_int.

Definition val_to_prod_int_int : val -> option (Z * Z) :=
  val_to_prod_of val_to_int val_to_int.

Definition eval_comp_to_list_of {A} (f : val -> option A) (fuel : nat) (c : comp) : val + list A :=
  let* v := eval_comp fuel c in
  match val_to_list_of f v with
  | None => inl (Failure "eval_comp_to_list_of")
  | Some xs => inr xs
  end.

Definition eval_comp_to_list_int : nat -> comp -> val + list Z :=
  eval_comp_to_list_of val_to_int.

Definition eval_comp_to_list_prod_int_int : nat -> comp -> val + list (Z * Z) :=
  eval_comp_to_list_of val_to_prod_int_int.
