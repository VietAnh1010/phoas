From Stdlib Require Import FunctionalExtensionality.
From shift_reset.monad Require Import ces_monad.

Lemma reset_idemp {R R' E S} (m : ces_monad R E S R) :
  @reset R R' E S (reset m) = @reset R R' E S m.
Proof.
  cbv. f_equal.
  apply functional_extensionality. intros k.
  apply functional_extensionality. intros s.
  destruct m as [m].
  destruct (m (fun x s => (inr x, s)) s) as [m' s'].
  destruct m' as [e | x].
  - reflexivity.
  - reflexivity.
Qed.

Lemma reset_bind_reset {R R' E S A} (m : ces_monad R E S A) (f : A -> ces_monad R E S R) :
  @reset R R' E S (bind m (fun x => (reset (f x)))) = @reset R R' E S (bind m f).
Proof.
  cbv. f_equal.
  apply functional_extensionality. intros k.
  apply functional_extensionality. intros s.
  destruct m as [m].
  apply (f_equal (fun k' =>
                    let (m, s) := m k' s in
                    match m with
                    | inl e => (inl e, s)
                    | inr x => k x s
                    end)).
  apply functional_extensionality. intros x.
  apply functional_extensionality. intros s'.
  destruct (f x) as [m'].
  destruct (m' (fun x s => (inr x, s)) s') as [m'' s''].
  destruct m'' as [e | x'].
  - reflexivity.
  - reflexivity.
Qed.
