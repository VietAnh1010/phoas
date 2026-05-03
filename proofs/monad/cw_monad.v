From Stdlib Require Import FunctionalExtensionality.
From shift_reset.monad Require Import signatures signatures_laws cw_monad.

Module Type MakeSig (W : Monoid).
  Include Make W.
End MakeSig.

Module MakeLaws (W : Monoid) (WLaws : MonoidLaws W) (MSig : MakeSig W).
  Import WLaws.
  Import MSig.

  Lemma reset_idemp {R R'} (m : cw_monad R W.t R) :
    @reset R R' (reset m) = reset m.
  Proof.
    cbv. f_equal.
    apply functional_extensionality. intros k.
    destruct m as [m].
    destruct (m (fun x => (x, W.empty))) as [x w].
    rewrite -> combine_empty_r.
    reflexivity.
  Qed.

  Lemma reset_bind_reset {R R' A} (m : cw_monad R W.t A) (f : A -> cw_monad R W.t R) :
    @reset R R' (bind m (fun x => (reset (f x)))) = reset (bind m f).
  Proof.
    cbv. f_equal.
    apply functional_extensionality. intros k.
    destruct m as [m].
    apply (f_equal (fun k' => let (x, w1) := m k' in let (y, w2) := k x in (y, W.combine w1 w2))).
    apply functional_extensionality. intros x.
    destruct (f x) as [m'].
    destruct (m' (fun x => (x, W.empty))) as [x' w].
    rewrite -> combine_empty_r.
    reflexivity.
  Qed.

  Lemma shift_reset {R R' A} (f : (A -> cw_monad R' W.t R) -> cw_monad R W.t R) :
    shift (fun k => reset (f k)) = shift f.
  Proof.
    cbv. f_equal.
    apply functional_extensionality. intros k.
    destruct (f (fun x => CWMonad (fun k' => let (y, w1) := k x in let (z, w2) := k' y in (z, W.combine w1 w2)))) as [m].
    destruct (m (fun x => (x, W.empty))) as [x w].
    rewrite -> combine_empty_r.
    reflexivity.
  Qed.
End MakeLaws.
