From Stdlib Require Import PArith.
From shift_reset.lib Require gmap.

Local Open Scope positive_scope.

Record loc : Type := Loc { loc_car : positive }.

Lemma loc_eq_dec : forall (l1 l2 : loc), {l1 = l2} + {l1 <> l2}.
Proof. decide equality; auto using Pos.eq_dec. Defined.

Definition loc_eqb (l1 l2 : loc) : bool :=
  Pos.eqb (loc_car l1) (loc_car l2).

Definition loc_neqb (l1 l2 : loc) : bool :=
  negb (loc_eqb l1 l2).

Definition loc_succ (l : loc) : loc :=
  Loc (Pos.succ (loc_car l)).

Definition loc_add (l : loc) (n : N) : loc :=
  match n with
  | N0 => l
  | Npos p => Loc (loc_car l + p)
  end.

Definition loc_init : loc := Loc 1.

Module IsoPositiveLoc <: gmap.IsoPositiveType.
  Definition t := loc.
  Definition encode := loc_car.
  Definition decode := Loc.

  Lemma decode_encode : forall x, decode (encode x) = x.
  Proof. exact (fun '(Loc _) => eq_refl). Qed.

  Lemma encode_decode : forall x, encode (decode x) = x.
  Proof. exact (fun _ => eq_refl). Qed.
End IsoPositiveLoc.

Module LocMap := gmap.Make (IsoPositiveLoc).
