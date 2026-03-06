From Stdlib Require Import List String ZArith.
From shift_reset.lib Require Import sum.
From shift_reset.core Require Import syntax syntax_notation ident.
From shift_reset.interpreter Require Import interpreter error.
Import ListNotations SumNotations.

Local Open Scope Z_scope.
Local Open Scope sum_scope.
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

Definition Reflect_failure : val -> exn :=
  Exn (Ident "Reflect_failure").

Fixpoint val_to_list {A} (f : val -> exn + A) (v : val) : exn + list A :=
  match v with
  | VInl VTt => inr []
  | VInr (VPair v1 v2) =>
      let* x := f v1 in
      cons x <$> val_to_list f v2
  | _ => inl (Reflect_failure v)
  end.

Definition eval_term_to_list {A} (f : val -> exn + A) (fuel : nat) (t : term) : exn + list A :=
  eval_term fuel t >>= val_to_list f.

Definition eval_term_to_list_int : nat -> term -> exn + list Z :=
  eval_term_to_list (fun v => match v with
                              | VInt z => inr z
                              | _ => inl (Reflect_failure v)
                              end).
