From Stdlib Require Import FunctionalExtensionality.
From shift_reset.monad Require Import cs_monad.

Lemma reset_idemp {R R' S} (m : cs_monad R S R) :
  @reset R R' S (reset m) = @reset R R' S m.
Proof.
  cbv. f_equal.
  apply functional_extensionality. intros k.
  apply functional_extensionality. intros s.
  destruct m as [m].
  destruct (m pair s) as [x s'].
  reflexivity.
Qed.

Lemma reset_bind_reset {R R' S A} (m : cs_monad R S A) (f : A -> cs_monad R S R) :
  @reset R R' S (bind m (fun x => (reset (f x)))) = @reset R R' S (bind m f).
Proof.
  cbv. f_equal.
  apply functional_extensionality. intros k.
  apply functional_extensionality. intros s.
  destruct m as [m].
  apply (f_equal (fun k' => let (x, s) := m k' s in k x s)).
  apply functional_extensionality. intros x.
  apply functional_extensionality. intros s'.
  destruct (f x) as [m'].
  destruct (m' pair s') as [x' s''].
  reflexivity.
Qed.

Lemma shift_reset {R R' S A} (f : (A -> cs_monad R' S R) -> cs_monad R S R) :
  shift (fun k => reset (f k)) = shift f.
Proof.
  cbv. f_equal.
  apply functional_extensionality. intros k.
  apply functional_extensionality. intros s.
  destruct (f (fun x => CSMonad (fun k' s => let (y, s) := k x s in k' y s))) as [m].
  destruct (m pair s) as [x s'].
  reflexivity.
Qed.
