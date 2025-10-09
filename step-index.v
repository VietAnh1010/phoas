Inductive expr :=
| EVar : nat -> expr
| EVal : val -> expr
| EApp : expr -> expr
with val :=
| VNat : nat -> val
| VFun : expr -> val.

Inductive type :=
| TyNat : type
| TyFun : type -> type -> type.

Axiom e_subst : expr -> val -> expr.

Axiom red_step : expr -> expr -> Prop.

Inductive red_steps_nat : nat -> expr -> expr -> Prop :=
| reds_refl : forall e, red_steps_nat O e e
| reds_step : forall n e1 e2 e3, red_step e1 e2 -> red_steps_nat n e2 e3 -> red_steps_nat (S n) e1 e3.

Definition red_steps_star (e1 e2 : expr) : Prop :=
  exists n, red_steps_nat n e1 e2.

Module S1.
  Definition E_aux (R : type -> val -> val -> Prop) (ty : type) (e1 e2 : expr) : Prop :=
    forall v1, red_steps_star e1 (EVal v1) -> exists v2, red_steps_star e2 (EVal v2) /\ R ty v1 v2.

  Fixpoint V (ty : type) (v1 v2 : val) : Prop :=
    match ty, v1, v2 with
    | TyNat, VNat n1, VNat n2 => n1 = n2
    | TyFun t s, VFun e1, VFun e2 => forall a1 a2, V t a1 a2 -> E_aux V s (e_subst e1 a1) (e_subst e2 a2)
    | _, _, _ => False
    end.

  Definition E : type -> expr -> expr -> Prop := E_aux V.
End S1.

From Stdlib Require Import Arith.

Module S2.

  Definition E_aux (k : nat) (R : forall i, i <= k -> type -> val -> val -> Prop) (ty : type) (e1 e2 : expr) : Prop :=
    forall (j : nat),
      j <= k ->
      forall (v1 : val),
        red_steps_nat j e1 (EVal v1) ->
        exists v2, red_steps_star e2 (EVal v2) /\ R (k - j) (Nat.le_sub_l _ _) ty v1 v2.

  Definition V_aux (k : nat) (R : forall i, i < k -> type -> val -> val -> Prop) (ty : type) (v1 v2 : val) : Prop :=
    match ty, v1, v2 with
    | TyNat, VNat n1, VNat n2 => n1 = n2
    | TyFun t s, VFun e1, VFun e2 =>
        forall (j : nat)
               (H_lt : j < k)
               (a1 a2 : val),
          R j H_lt t a1 a2 ->
          E_aux j (fun i H_le => R i (Nat.le_lt_trans _ _ _ H_le H_lt)) s (e_subst e1 a1) (e_subst e2 a2)
    | _, _, _ => False
    end.

  Definition V (k : nat) : type -> val -> val -> Prop := lt_wf_rect k _ V_aux.
  Definition E (k : nat) : type -> expr -> expr -> Prop := E_aux k (fun j _ => V j).
End S2.
