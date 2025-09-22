From Stdlib Require Import PArith.
From shift_reset Require option.

Local Open Scope positive_scope.
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Inductive pmap_ne (A : Type) :=
| PNode001 : pmap_ne A -> pmap_ne A
| PNode010 : A -> pmap_ne A
| PNode011 : A -> pmap_ne A -> pmap_ne A
| PNode100 : pmap_ne A -> pmap_ne A
| PNode101 : pmap_ne A -> pmap_ne A -> pmap_ne A
| PNode110 : pmap_ne A -> A -> pmap_ne A
| PNode111 : pmap_ne A -> A -> pmap_ne A -> pmap_ne A.

Inductive pmap (A : Type) :=
| PEmpty : pmap A
| PNodes : pmap_ne A -> pmap A.

Arguments PNode001 {A} _.
Arguments PNode010 {A} _.
Arguments PNode011 {A} _ _.
Arguments PNode100 {A} _.
Arguments PNode101 {A} _ _.
Arguments PNode110 {A} _ _.
Arguments PNode111 {A} _ _ _.

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

Definition pmap_ne_case {A B} (t : pmap_ne A) (f : pmap A -> option A -> pmap A -> B) : B :=
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

Fixpoint ne_lookup {A} (i : positive) (t : pmap_ne A) {struct t} : option A :=
  match t, i with
  | (PNode010 x | PNode011 x _ | PNode110 _ x | PNode111 _ x _), 1 => Some x
  | (PNode100 l | PNode110 l _ | PNode101 l _ | PNode111 l _ _), i~0 => ne_lookup i l
  | (PNode001 r | PNode011 _ r | PNode101 _ r | PNode111 _ _ r), i~1 => ne_lookup i r
  | _, _ => None
  end.

Definition lookup {A} (i : positive) (mt : pmap A) : option A :=
  match mt with
  | PEmpty => None
  | PNodes t => ne_lookup i t
  end.

Fixpoint ne_member {A} (i : positive) (t : pmap_ne A) {struct t} : bool :=
  match t, i with
  | (PNode010 _ | PNode011 _ _ | PNode110 _ _ | PNode111 _ _ _), 1 => true
  | (PNode100 l | PNode110 l _ | PNode101 l _ | PNode111 l _ _), i~0 => ne_member i l
  | (PNode001 r | PNode011 _ r | PNode101 _ r | PNode111 _ _ r), i~1 => ne_member i r
  | _, _ => false
  end.

Definition member {A} (i : positive) (mt : pmap A) : bool :=
  match mt with
  | PEmpty => false
  | PNodes t => ne_member i t
  end.

Definition ne_singleton {A} (i : positive) (x : A) : pmap_ne A :=
  let fix go i :=
    match i with
    | 1 => PNode010 x
    | i~0 => PNode100 (go i)
    | i~1 => PNode001 (go i)
    end
  in go i.

Definition singleton {A} (i : positive) (x : A) : pmap A :=
  PNodes (ne_singleton i x).

Definition ne_insert {A} (i : positive) (x : A) : pmap_ne A -> pmap_ne A :=
  let fix go i t {struct t} :=
    match t with
    | PNode001 r =>
        match i with
        | 1 => PNode011 x r
        | i~0 => PNode101 (ne_singleton i x) r
        | i~1 => PNode001 (go i r)
        end
    | PNode010 y =>
        match i with
        | 1 => PNode010 x
        | i~0 => PNode110 (ne_singleton i x) y
        | i~1 => PNode011 y (ne_singleton i x)
        end
    | PNode011 y r =>
        match i with
        | 1 => PNode011 x r
        | i~0 => PNode111 (ne_singleton i x) y r
        | i~1 => PNode011 y (go i r)
        end
    | PNode100 l =>
        match i with
        | 1 => PNode110 l x
        | i~0 => PNode100 (go i l)
        | i~1 => PNode101 l (ne_singleton i x)
        end
    | PNode101 l r =>
        match i with
        | 1 => PNode111 l x r
        | i~0 => PNode101 (go i l) r
        | i~1 => PNode101 l (go i r)
        end
    | PNode110 l y =>
        match i with
        | 1 => PNode110 l x
        | i~0 => PNode110 (go i l) y
        | i~1 => PNode111 l y (ne_singleton i x)
        end
    | PNode111 l y r =>
        match i with
        | 1 => PNode111 l x r
        | i~0 => PNode111 (go i l) y r
        | i~1 => PNode111 l y (go i r)
        end
    end
  in go i.

Definition insert {A} (i : positive) (x : A) (mt : pmap A) : pmap A :=
  match mt with
  | PEmpty => singleton i x
  | PNodes t => PNodes (ne_insert i x t)
  end.

Definition remove_aux {A} (go : positive -> pmap_ne A -> pmap A) (i : positive) (mt : pmap A) : pmap A :=
  match mt with
  | PEmpty => PEmpty
  | PNodes t => go i t
  end.

Fixpoint ne_remove {A} (i : positive) (t : pmap_ne A) {struct t} : pmap A :=
  pmap_ne_case t
    (fun ml mx mr => match i with
                     | 1 => PNode ml None mr
                     | i~0 => PNode (remove_aux ne_remove i ml) mx mr
                     | i~1 => PNode ml mx (remove_aux ne_remove i mr)
                     end).

Definition remove {A} : positive -> pmap A -> pmap A :=
  remove_aux ne_remove.

Definition alter_aux {A} (go : positive -> pmap_ne A -> pmap A) (f : option A -> option A) (i : positive) (mt : pmap A) : pmap A :=
  match mt with
  | PEmpty => match f None with
              | None => PEmpty
              | Some x => singleton i x
              end
  | PNodes t => go i t
  end.

Definition ne_alter {A} (f : option A -> option A) : positive -> pmap_ne A -> pmap A :=
  fix go i t {struct t} :=
    pmap_ne_case t
      (fun ml mx mr => match i with
                       | 1 => PNode ml (f mx) mr
                       | i~0 => PNode (alter_aux go f i ml) mx mr
                       | i~1 => PNode ml mx (alter_aux go f i mr)
                       end).

Definition alter {A} (f : option A -> option A) : positive -> pmap A -> pmap A :=
  alter_aux (ne_alter f) f.

Definition ne_map {A B} (f : A -> B) : pmap_ne A -> pmap_ne B :=
  fix go t :=
    match t with
    | PNode001 r => PNode001 (go r)
    | PNode010 x => PNode010 (f x)
    | PNode011 x r => PNode011 (f x) (go r)
    | PNode100 l => PNode100 (go l)
    | PNode101 l r => PNode101 (go l) (go r)
    | PNode110 l x => PNode110 (go l) (f x)
    | PNode111 l x r => PNode111 (go l) (f x) (go r)
    end.

Definition map {A B} (f : A -> B) (mt : pmap A) : pmap B :=
  match mt with
  | PEmpty => PEmpty
  | PNodes t => PNodes (ne_map f t)
  end.

Definition filter_map_aux {A B} (go : pmap_ne A -> pmap B) (mt : pmap A) : pmap B :=
  match mt with
  | PEmpty => PEmpty
  | PNodes t => go t
  end.

Definition ne_filter_map {A B} (f : A -> option B) : pmap_ne A -> pmap B :=
  fix go t :=
    pmap_ne_case t
      (fun ml mx mr => PNode
                         (filter_map_aux go ml)
                         (option.bind mx f)
                         (filter_map_aux go mr)).

Definition filter_map {A B} (f : A -> option B) : pmap A -> pmap B :=
  filter_map_aux (ne_filter_map f).
