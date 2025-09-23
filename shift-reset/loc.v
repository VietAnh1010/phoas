From Stdlib Require Import NArith.
From shift_reset Require gmap.

Record loc : Type := Loc { loc_car : N }.

Definition loc_eq_dec : forall (l1 l2 : loc), {l1 = l2} + {l1 <> l2}.
Proof. decide equality; auto using N.eq_dec. Defined.

Definition succ (l : loc) : loc :=
  Loc (N.succ (loc_car l)).

Module IsoPositiveLoc <: gmap.IsoPositiveType.
  Definition t := loc.
  Definition encode x := N.succ_pos (loc_car x).
  Definition decode x := Loc (Pos.pred_N x).

  Lemma decode_encode : forall x, decode (encode x) = x.
  Proof.
    intros [x].
    unfold decode, encode, loc_car.
    exact (f_equal Loc (N.pos_pred_succ x)).
  Qed.

  Lemma encode_decode : forall x, encode (decode x) = x.
  Proof.
    intros x.
    unfold encode, decode, loc_car.
    destruct x as [x' | x' |].
    - simpl. reflexivity.
    - simpl. exact (Pos.succ_pred_double x').
    - simpl. reflexivity.
  Qed.
End IsoPositiveLoc.

Module LocMap := gmap.Make (IsoPositiveLoc).
