From Stdlib Require Import FunctionalExtensionality.
From shift_reset.monad Require Import lr_monad.

Lemma map_id {R A} (m : lr_monad R A) :
  map (fun x => x) m = m.
Proof.
  revert m. fix IH 1.
  intros [m]. cbn. f_equal.
  apply functional_extensionality. intros r.
  destruct (m r) as [| x m'].
  - reflexivity.
  - rewrite -> (IH m').
    reflexivity.
Qed.

Lemma map_comp {R A B C} (f : B -> C) (g : A -> B) (m : lr_monad R A) :
  map f (map g m) = map (fun x => f (g x)) m.
Proof.
  revert m. fix IH 1.
  intros [m]. cbn. f_equal.
  apply functional_extensionality. intros r.
  destruct (m r) as [| x m'].
  - reflexivity.
  - rewrite -> (IH m').
    reflexivity.
Qed.

Lemma combine_empty_l {R A} (m : lr_monad R A) :
  combine empty m = m.
Proof. destruct m as [m]. cbn. reflexivity. Qed.

Lemma combine_empty_r {R A} (m : lr_monad R A) :
  combine m empty = m.
Proof.
  revert m. fix IH 1.
  intros [m]. cbn. f_equal.
  apply functional_extensionality. intros r.
  destruct (m r) as [| x m'].
  - reflexivity.
  - rewrite -> (IH m').
    reflexivity.
Qed.

Lemma combine_assoc {R A} (m1 m2 m3 : lr_monad R A) :
  combine (combine m1 m2) m3 = combine m1 (combine m2 m3).
Proof.
  revert m1 m2. fix IH 1.
  intros [m1] m2. cbn. f_equal.
  apply functional_extensionality. intros r.
  destruct (m1 r) as [| x m1'].
  - destruct m2 as [m2]. cbn.
    reflexivity.
  - rewrite -> (IH m1' m2).
    reflexivity.
Qed.

Lemma bind_combine_distr {R A B} (m1 m2 : lr_monad R A) (f : A -> lr_monad R B) :
  bind (combine m1 m2) f = combine (bind m1 f) (bind m2 f).
Proof.
  revert m1 m2. fix IH 1.
  intros [m1] m2. cbn. f_equal.
  apply functional_extensionality. intros r.
  destruct (m1 r) as [| x m1'].
  - destruct m2 as [m2]. cbn.
    reflexivity.
  - rewrite -> (IH m1' m2).
    rewrite <- combine_assoc.
    destruct (combine (f x) (bind m1' f)) as [m]. cbn.
    reflexivity.
Qed.

Lemma empty_bind {R A B} (f : A -> lr_monad R B) :
  bind empty f = empty.
Proof. cbn. reflexivity. Qed.

Lemma pure_bind {R A B} (x : A) (f : A -> lr_monad R B) :
  bind (pure x) f = f x.
Proof.
  cbn. fold (@empty R B).
  destruct (f x) as [m]. cbn. f_equal.
  apply functional_extensionality. intros r.
  destruct (m r) as [| x' m'].
  - reflexivity.
  - rewrite -> combine_empty_r.
    reflexivity.
Qed.

Lemma bind_pure {R A} (m : lr_monad R A) :
  bind m pure = m.
Proof.
  revert m. fix IH 1.
  intros [m]. cbn. f_equal.
  apply functional_extensionality. intros r.
  destruct (m r) as [| x m'].
  - reflexivity.
  - rewrite -> (IH m').
    destruct m' as [m']. cbn.
    reflexivity.
Qed.

Lemma bind_assoc {R A B C} (m : lr_monad R A) (f : A -> lr_monad R B) (g : B -> lr_monad R C) :
  bind (bind m f) g = bind m (fun x => bind (f x) g).
Proof.
  revert m. fix IH 1.
  intros [m]. cbn. f_equal.
  apply functional_extensionality. intros r.
  destruct (m r) as [| x m'].
  - reflexivity.
  - rewrite <- (IH m').
    rewrite <- (bind_combine_distr).
    destruct (combine (f x) (bind m' f)) as [m'']. cbn.
    reflexivity.
Qed.
