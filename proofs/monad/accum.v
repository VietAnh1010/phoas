From Stdlib Require Import FunctionalExtensionality.
From shift_reset.lib Require Import signatures signature_laws.
From shift_reset.monad Require Import accum.

Lemma map_id {W A} (m : accum W A) :
  map (fun x => x) m = m.
Proof.
  cbv. destruct m as [m]. f_equal.
  apply functional_extensionality. intros w.
  destruct (m w) as [x w'].
  reflexivity.
Qed.

Lemma map_comp {W A B C} (f : B -> C) (g : A -> B) (m : accum W A) :
  map f (map g m) = map (fun x => f (g x)) m.
Proof.
  cbv. f_equal.
  apply functional_extensionality. intros w.
  destruct m as [m].
  destruct (m w) as [x w'].
  reflexivity.
Qed.

Module Type MakeSig (W : Monoid).
  Include Make W.
End MakeSig.

Module MakeLaws (W : Monoid) (WLaws : MonoidLaws W) (MSig : MakeSig W).
  Import WLaws.
  Import MSig.

  Lemma pure_bind {A B} (x : A) (f : A -> accum W.t B) :
    bind (pure x) f = f x.
  Proof.
    cbv. destruct (f x) as [m]. f_equal.
    apply functional_extensionality. intros w.
    rewrite -> append_empty_r.
    destruct (m w) as [y w'].
    rewrite -> append_empty_l.
    reflexivity.
  Qed.

  Lemma bind_pure {A} (m : accum W.t A) :
    bind m pure = m.
  Proof.
    cbv. destruct m as [m]. f_equal.
    apply functional_extensionality. intros w.
    destruct (m w) as [x w'].
    rewrite -> append_empty_r.
    reflexivity.
  Qed.

  Lemma bind_assoc {A B C} (m : accum W.t A) (f : A -> accum W.t B) (g : B -> accum W.t C) :
    bind (bind m f) g = bind m (fun x => bind (f x) g).
  Proof.
    cbv. f_equal.
    apply functional_extensionality. intros w.
    destruct m as [m].
    destruct (m w) as [x w'].
    destruct (f x) as [m'].
    destruct (m' (W.append w w')) as [y w''].
    destruct (g y) as [m''].
    rewrite -> append_assoc.
    destruct (m'' (W.append w (W.append w' w''))) as [z w'''].
    rewrite -> append_assoc.
    reflexivity.
  Qed.
End MakeLaws.
