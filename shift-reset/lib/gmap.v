From Stdlib Require Import PArith.
From shift_reset.lib Require pmap.

Module Type IsoPositiveType.
  Parameter t : Type.
  Parameter encode : t -> positive.
  Parameter decode : positive -> t.
  Axiom decode_encode : forall (x : t), decode (encode x) = x.
  Axiom encode_decode : forall (x : positive), encode (decode x) = x.
End IsoPositiveType.

Record gmap (K A : Type) := GMap { gmap_car : pmap.pmap A }.

Arguments GMap {K A} _.
Arguments gmap_car {K A} _.

Definition empty {K A} : gmap K A := GMap pmap.empty.

Definition map {K A B} (f : A -> B) (mt : gmap K A) : gmap K B :=
  GMap (pmap.map f (gmap_car mt)).

Definition filter_map {K A B} (f : A -> option B) (mt : gmap K A) : gmap K B :=
  GMap (pmap.filter_map f (gmap_car mt)).

Module Make (K : IsoPositiveType).
  Definition key : Type := K.t.
  Definition t : Type -> Type := gmap key.

  Definition lookup {A} (k : key) (mt : gmap key A) : option A :=
    pmap.lookup (K.encode k) (gmap_car mt).

  Definition member {A} (k : key) (mt : gmap key A) : bool :=
    pmap.member (K.encode k) (gmap_car mt).

  Definition singleton {A} (k : key) (x : A) : gmap key A :=
    GMap (pmap.singleton (K.encode k) x).

  Definition insert {A} (k : key) (x : A) (mt : gmap key A) : gmap key A :=
    GMap (pmap.insert (K.encode k) x (gmap_car mt)).

  Definition remove {A} (k : key) (mt : gmap key A) : gmap key A :=
    GMap (pmap.remove (K.encode k) (gmap_car mt)).

  Definition alter {A} (f : option A -> option A) (k : key) (mt : gmap key A) : gmap key A :=
    GMap (pmap.alter f (K.encode k) (gmap_car mt)).
End Make.
