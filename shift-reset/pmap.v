From Stdlib Require Import PArith.

Local Open Scope positive_scope.

Inductive pmap_ne (A : Type) :=
| PNode001 : pmap_ne A -> pmap_ne A
| PNode010 : A -> pmap_ne A
| PNode011 : A -> pmap_ne A -> pmap_ne A
| PNode100 : pmap_ne A -> pmap_ne A
| PNode101 : pmap_ne A -> pmap_ne A -> pmap_ne A
| PNode110 : pmap_ne A -> A -> pmap_ne A
| PNode111 : pmap_ne A -> A -> pmap_ne A -> pmap_ne A.

Arguments PNode001 {A} _.
Arguments PNode010 {A} _.
Arguments PNode011 {A} _ _.
Arguments PNode100 {A} _.
Arguments PNode101 {A} _ _.
Arguments PNode110 {A} _ _.
Arguments PNode111 {A} _ _ _.

Variant pmap (A : Type) :=
| PEmpty : pmap A
| PNodes : pmap_ne A -> pmap A.

Arguments PEmpty {A}.
Arguments PNodes {A} _.

Definition PNode {A} (ml : pmap A) (mx : option A) (mr : pmap A) : pmap A :=
  match ml, mx, mr with
  | PEmpty, None, PEmpty => PEmpty
  | PEmpty, None, PNodes r => PNodes (PNode001 r)
  | PEmpty, Some x, PEmpty => PNodes (PNode010 x)
  | PEmpty, Some x, PNodes r => PNodes (PNode011 x r)
  | PNodes l, None, PEmpty => PNodes (PNode100 l)
  | PNodes l, None, PNodes r => PNodes (PNode101 l r)
  | PNodes l, Some x, PEmpty => PNodes (PNode110 l x)
  | PNodes l, Some x, PNodes r => PNodes (PNode111 l x r)
  end.

Definition ne_case {A B} (t : pmap_ne A) (f : pmap A -> option A -> pmap A -> B) : B :=
  match t with
  | PNode001 r => f PEmpty None (PNodes r)
  | PNode010 x => f PEmpty (Some x) PEmpty
  | PNode011 x r => f PEmpty (Some x) (PNodes r)
  | PNode100 l => f (PNodes l) None PEmpty
  | PNode101 l r => f (PNodes l) None (PNodes r)
  | PNode110 l x => f (PNodes l) (Some x) PEmpty
  | PNode111 l x r => f (PNodes l) (Some x) (PNodes r)
  end.

Definition empty {A} : pmap A := PEmpty.

Fixpoint ne_get {A} (i : positive) (t : pmap_ne A) : option A.
Admitted.

Definition get {A} (i : positive) (mt : pmap A) : option A :=
  match mt with
  | PEmpty => None
  | PNodes t => ne_get i t
  end.

Fixpoint ne_singleton {A} (i : positive) (x : A) : pmap_ne A :=
  match i with
  | 1 => PNode010 x
  | i~0 => PNode100 (ne_singleton i x)
  | i~1 => PNode001 (ne_singleton i x)
  end.
