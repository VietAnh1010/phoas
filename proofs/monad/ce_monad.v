From Stdlib Require Import FunctionalExtensionality.
From shift_reset.monad Require Import ce_monad.

Lemma reset_idemp {R R' E} (m : ce_monad R E R) :
  @reset R R' E (reset m) = @reset R R' E m.
Proof.
  cbv. f_equal.
  destruct m as [m].
  destruct (m inr) as [e | x].
  - reflexivity.
  - reflexivity.
Qed.

Lemma reset_bind_reset {R R' E A} (m : ce_monad R E A) (f : A -> ce_monad R E R) :
  @reset R R' E (bind m (fun x => (reset (f x)))) = @reset R R' E (bind m f).
Proof.
  cbv. f_equal.
  apply functional_extensionality. intros k.
  destruct m as [m].
  apply (f_equal (fun k' =>
                    match m k' with
                    | inl e => inl e
                    | inr x => k x
                    end)).
  apply functional_extensionality. intros x.
  destruct (f x) as [m'].
  destruct (m' inr) as [e | x'].
  - reflexivity.
  - reflexivity.
Qed.
