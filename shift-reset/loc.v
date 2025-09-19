From Stdlib Require Import OrderedType Arith.

Inductive loc : Type := Loc : nat -> loc.
Definition unloc (l : loc) : nat := match l with Loc n => n end.

Module LocOrderedType <: OrderedType.
  Definition t : Type := loc.

  Definition eq (l1 l2 : loc) : Prop := Nat.eq (unloc l1) (unloc l2).
  Definition lt (l1 l2 : loc) : Prop := Nat.lt (unloc l1) (unloc l2).

  Theorem eq_refl : forall x : t, eq x x.
  Proof. intros [x]. apply Nat.eq_refl. Qed.

  Theorem eq_sym : forall x y : t, eq x y -> eq y x.
  Proof. intros [x] [y]. apply Nat.eq_sym. Qed.

  Theorem eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof. intros [x] [y] [z]. apply Nat.eq_trans. Qed.

  Theorem lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof. intros [x] [y] [z]. apply Nat.lt_trans. Qed.

  Theorem lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof. intros [x] [y]. apply Nat.lt_neq. Qed.

  Theorem compare : forall x y : t, OrderedType.Compare lt eq x y.
  Proof.
    intros [x] [y].
    destruct (lt_eq_lt_dec x y) as [[H_lt | H_eq] | H_gt].
    - apply LT. exact H_lt.
    - apply EQ. exact H_eq.
    - apply GT. exact H_gt.
  Defined.

  Theorem eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof. intros [x] [y]. apply Nat.eq_dec. Defined.
End LocOrderedType.
