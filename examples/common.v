From Stdlib Require Import List String ZArith.
From shift_reset.lib Require Import option sum.
From shift_reset.core Require Import syntax syntax_notation ident val.
From shift_reset.interpreter Require Import interpreter error.
Import ListNotations OptionNotations SumNotations.

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

Fixpoint list_to_val_term {A} (f : A -> val_term) (xs : list A) : val_term :=
  match xs with
  | [] => <{ Inl () }>
  | x :: xs' => <{ Inr ({f x}, {list_to_val_term f xs'}) }>
  end.

Definition list_int_to_val_term : list Z -> val_term :=
  list_to_val_term TVInt.

Fixpoint deep_val_to_list {A} (f : val -> option A) (v : val) : option (list A) :=
  match v with
  | VInl VTt => Some []
  | VInr (VPair v1 v2) =>
      let* x := f v1 in
      cons x <$> deep_val_to_list f v2
  | _ => None
  end%option.

Definition val_to_list_int : val -> option (list Z) :=
  deep_val_to_list val_to_int.

Definition val_to_prod_int_int (v : val) : option (Z * Z) :=
  match v with
  | VPair (VInt z1) (VInt z2) => Some (z1, z2)
  | _ => None
  end.

Definition deep_eval_term_to_list {A} (f : val -> option A) (fuel : nat) (t : term) : val + list A :=
  let* v := eval_term fuel t in
  match deep_val_to_list f v with
  | None => inl (Failure "deep_eval_term_to_list")
  | Some xs => inr xs
  end%sum.

Definition eval_term_to_list_int : nat -> term -> val + list Z :=
  deep_eval_term_to_list val_to_int.

Definition eval_term_to_list_prod_int_int : nat -> term -> val + list (Z * Z) :=
  deep_eval_term_to_list val_to_prod_int_int.
