From shift_reset.monad Require Import signatures signatures_laws writer.

Lemma map_id {W A} (m : writer W A) :
  map (fun x => x) m = m.
Proof.
  cbv.
  destruct m as [m].
  destruct m as [x w].
  reflexivity.
Qed.

Lemma map_comp {W A B C} (f : B -> C) (g : A -> B) (m : writer W A) :
  map f (map g m) = map (fun x => f (g x)) m.
Proof.
  cbv. f_equal.
  destruct m as [m].
  destruct m as [x w].
  reflexivity.
Qed.

Module Type MakeSig (W : Monoid).
  Include Make W.
End MakeSig.

Module MakeLaws (W : Monoid) (WLaws : MonoidLaws W) (MSig : MakeSig W).
  Import WLaws.
  Import MSig.

  Lemma pure_bind {A B} (x : A) (f : A -> writer W.t B) :
    bind (pure x) f = f x.
  Proof.
    cbv.
    destruct (f x) as [m].
    destruct m as [y w].
    rewrite -> combine_empty_l.
    reflexivity.
  Qed.

  Lemma bind_pure {A} (m : writer W.t A) :
    bind m pure = m.
  Proof.
    cbv.
    destruct m as [m].
    destruct m as [x w].
    rewrite -> combine_empty_r.
    reflexivity.
  Qed.

  Lemma bind_assoc {A B C} (m : writer W.t A) (f : A -> writer W.t B) (g : B -> writer W.t C) :
    bind (bind m f) g = bind m (fun x => bind (f x) g).
  Proof.
    cbv. f_equal.
    destruct m as [m].
    destruct m as [x w].
    destruct (f x) as [m].
    destruct m as [y w'].
    destruct (g y) as [m].
    destruct m as [z w''].
    rewrite -> combine_assoc.
    reflexivity.
  Qed.
End MakeLaws.
