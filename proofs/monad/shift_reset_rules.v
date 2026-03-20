From Stdlib Require Import FunctionalExtensionality.

From shift_reset.monad Require Import cont.

Lemma cont_reset_reset {R R'} (m : cont R R) :
  @reset R R' (reset m) =
  @reset R R' m.
Proof. cbv. reflexivity. Qed.

Lemma cont_reset_bind_reset {R R' A} (m : cont R A) (k : A -> cont R R) :
  @reset R R' (bind m (fun x => (reset (k x)))) =
  @reset R R' (bind m k).
Proof. cbv. reflexivity. Qed.

From shift_reset.monad Require Import ces_monad.

Lemma ces_monad_reset_reset {R R' E S} (m : ces_monad R E S R) :
  @reset R R' E S (reset m) =
  @reset R R' E S m.
Proof.
  cbv. f_equal. destruct m as [m].
  apply functional_extensionality. intros k.
  apply functional_extensionality. intros s.
  destruct (m (fun x s => (inr x, s)) s) as [m' s'].
  destruct m' as [e | x]; reflexivity.
Qed.

Lemma ces_monad_reset_bind_reset {R R' E S A} (m : ces_monad R E S A) (k : A -> ces_monad R E S R) :
  @reset R R' E S (bind m (fun x => (reset (k x)))) =
  @reset R R' E S (bind m k).
Proof.
  cbv. f_equal. destruct m as [m].
  apply functional_extensionality. intros k'.
  apply functional_extensionality. intros s.
  apply (f_equal (fun f =>
                    let (m, s) := m f s in
                    match m with
                    | inl e => (inl e, s)
                    | inr x => k' x s
                    end)).
  apply functional_extensionality. intros x.
  apply functional_extensionality. intros s'.
  destruct (k x) as [m'].
  destruct (m' (fun x s => (inr x, s)) s') as [m'' s''].
  destruct m'' as [e | x']; reflexivity.
Qed.

From shift_reset.monad Require Import ce_monad.

Lemma ce_monad_reset_reset {R R' E} (m : ce_monad R E R) :
  @reset R R' E (reset m) =
  @reset R R' E m.
Proof.
  cbv. f_equal.
  destruct m as [m].
  destruct (m inr) as [e | x]; reflexivity.
Qed.

Lemma ce_monad_reset_bind_reset {R R' E A} (m : ce_monad R E A) (k : A -> ce_monad R E R) :
  @reset R R' E (bind m (fun x => (reset (k x)))) =
  @reset R R' E (bind m k).
Proof.
  cbv. f_equal. destruct m as [m].
  apply functional_extensionality. intros k'.
  apply (f_equal (fun f =>
                    match m f with
                    | inl e => inl e
                    | inr x => k' x
                    end)).
  apply functional_extensionality. intros x.
  destruct (k x) as [m'].
  destruct (m' inr) as [e | x']; reflexivity.
Qed.

From shift_reset.monad Require Import cs_monad.

Lemma cs_monad_reset_reset {R R' S} (m : cs_monad R S R) :
  @reset R R' S (reset m) =
  @reset R R' S m.
Proof.
  cbv. f_equal. destruct m as [m].
  apply functional_extensionality. intros k.
  apply functional_extensionality. intros s.
  destruct (m pair s) as [x s'].
  reflexivity.
Qed.

Lemma cs_monad_reset_bind_reset {R R' S A} (m : cs_monad R S A) (k : A -> cs_monad R S R) :
  @reset R R' S (bind m (fun x => (reset (k x)))) =
  @reset R R' S (bind m k).
Proof.
  cbv. f_equal. destruct m as [m].
  apply functional_extensionality. intros k'.
  apply functional_extensionality. intros s.
  apply (f_equal (fun f => let (x, s) := m f s in k' x s)).
  apply functional_extensionality. intros x.
  apply functional_extensionality. intros s'.
  destruct (k x) as [m'].
  destruct (m' pair s') as [x' s''].
  reflexivity.
Qed.

Lemma cs_monad_shift_reset {R R' S A} (f : (A -> cs_monad R' S R) -> cs_monad R S R) :
  shift (fun k => reset (f k)) =
  shift f.
Proof.
  cbv. f_equal.
  apply functional_extensionality. intros k.
  apply functional_extensionality. intros s.
  destruct (f _) as [m].
  destruct (m pair s) as [x s'].
  reflexivity.
Qed.
