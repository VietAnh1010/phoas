From Stdlib Require Import PArith.
From shift_reset.lib Require pmap.

Module Type IsoPositiveType.
  Parameter t : Type.
  Parameter encode : t -> positive.
  Parameter decode : positive -> t.
  Axiom decode_encode : forall (x : t), decode (encode x) = x.
  Axiom encode_decode : forall (x : positive), encode (decode x) = x.
End IsoPositiveType.

Record gmap (K A : Type) := GMap { gmap_car : pmap.t A }.
Definition t : Type -> Type -> Type := gmap.

Arguments GMap {K A} _.
Arguments gmap_car {K A} _.

Definition empty {K A} : gmap K A := GMap pmap.empty.

Definition is_empty {K A} (mt : gmap K A) : bool :=
  pmap.is_empty (gmap_car mt).

Definition is_singleton {K A} (mt : gmap K A) : bool :=
  pmap.is_singleton (gmap_car mt).

Definition map {K A B} (f : A -> B) (mt : gmap K A) : gmap K B :=
  GMap (pmap.map f (gmap_car mt)).

Definition filter {K A} (f : A -> bool) (mt : gmap K A) : gmap K A :=
  GMap (pmap.filter f (gmap_car mt)).

Definition filter_map {K A B} (f : A -> option B) (mt : gmap K A) : gmap K B :=
  GMap (pmap.filter_map f (gmap_car mt)).

Definition cardinal {K A} (mt : gmap K A) : nat :=
  pmap.cardinal (gmap_car mt).

Module Make (K : IsoPositiveType).
  Definition find {A} (k : K.t) (mt : gmap K.t A) : option A :=
    pmap.find (K.encode k) (gmap_car mt).

  Definition member {A} (k : K.t) (mt : gmap K.t A) : bool :=
    pmap.member (K.encode k) (gmap_car mt).

  Definition singleton {A} (k : K.t) (x : A) : gmap K.t A :=
    GMap (pmap.singleton (K.encode k) x).

  Definition add {A} (k : K.t) (x : A) (mt : gmap K.t A) : gmap K.t A :=
    GMap (pmap.add (K.encode k) x (gmap_car mt)).

  Definition remove {A} (k : K.t) (mt : gmap K.t A) : gmap K.t A :=
    GMap (pmap.remove (K.encode k) (gmap_car mt)).

  Definition update {A} (k : K.t) (f : option A -> option A) (mt : gmap K.t A) : gmap K.t A :=
    GMap (pmap.update (K.encode k) f (gmap_car mt)).

  Definition mapi {A B} (f : K.t -> A -> B) (mt : gmap K.t A) : gmap K.t B :=
    GMap (pmap.mapi (fun i => f (K.decode i)) (gmap_car mt)).

  Definition filter_mapi {A B} (f : K.t -> A -> option B) (mt : gmap K.t A) : gmap K.t B :=
    GMap (pmap.filter_mapi (fun i => f (K.decode i)) (gmap_car mt)).

  Definition merge {A B C} (f : K.t -> option A -> option B -> option C) (mt1 : gmap K.t A) (mt2 : gmap K.t B) : gmap K.t C :=
    GMap (pmap.merge (fun i => f (K.decode i)) (gmap_car mt1) (gmap_car mt2)).
End Make.
