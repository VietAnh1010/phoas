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

Definition map {K A B} (f : A -> B) (mt : gmap K A) : gmap K B :=
  GMap (pmap.map f (gmap_car mt)).

Definition filter_map {K A B} (f : A -> option B) (mt : gmap K A) : gmap K B :=
  GMap (pmap.filter_map f (gmap_car mt)).

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
End Make.
