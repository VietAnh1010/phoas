From Stdlib Require Import PArith.
From shift_reset Require pmap.

Module Type IsoPositiveType.
  Parameter t : Type.
  Parameter encode : t -> positive.
  Parameter decode : positive -> t.
  Axiom decode_encode : forall (x : t), decode (encode x) = x.
  Axiom encode_decode : forall (x : positive), encode (decode x) = x.
End IsoPositiveType.

Module Make (K : IsoPositiveType).
  Definition key : Type := K.t.
  Record gmap (A : Type) := GMap { gmap_car : pmap.pmap A }.
  Definition t : Type -> Type := gmap.

  Arguments GMap {A} _.
  Arguments gmap_car {A} _.

  Definition empty {A} : gmap A := GMap pmap.empty.

  Definition lookup {A} (k : key) (mt : t A) : option A :=
    pmap.lookup (K.encode k) (gmap_car mt).

  Definition member {A} (k : key) (mt : t A) : bool :=
    pmap.member (K.encode k) (gmap_car mt).

  Definition singleton {A} (k : key) (x : A) : t A :=
    GMap (pmap.singleton (K.encode k) x).

  Definition insert {A} (k : key) (x : A) (mt : t A) : t A :=
    GMap (pmap.insert (K.encode k) x (gmap_car mt)).

  Definition remove {A} (k : key) (mt : t A) : t A :=
    GMap (pmap.remove (K.encode k) (gmap_car mt)).

  Definition alter {A} (f : option A -> option A) (k : key) (mt : t A) : t A :=
    GMap (pmap.alter f (K.encode k) (gmap_car mt)).

  Definition map {A B} (f : A -> B) (mt : t A) : t B :=
    GMap (pmap.map f (gmap_car mt)).

  Definition filter_map {A B} (f : A -> option B) (mt : t A) : t B :=
    GMap (pmap.filter_map f (gmap_car mt)).
End Make.
