From Stdlib Require Import FunctionalExtensionality.
From shift_reset.monad Require Import ls_monad.

Lemma map_id {S A} (m : ls_monad S A) :
  map (fun x => x) m = m.
Proof.
  revert m. fix IH 1.
  intros [m]. cbn. f_equal.
  apply functional_extensionality. intros s.
  destruct (m s) as [m' s'].
  destruct m' as [| x m'].
  - reflexivity.
  - rewrite -> (IH m').
    reflexivity.
Qed.

Lemma map_comp {S A B C} (f : B -> C) (g : A -> B) (m : ls_monad S A) :
  map f (map g m) = map (fun x => f (g x)) m.
Proof.
  revert m. fix IH 1.
  intros [m]. cbn. f_equal.
  apply functional_extensionality. intros s.
  destruct (m s) as [m' s'].
  destruct m' as [| x m'].
  - reflexivity.
  - rewrite -> (IH m').
    reflexivity.
Qed.

Lemma combine_empty_l {S A} (m : ls_monad S A) :
  combine empty m = m.
Proof. destruct m as [m]. cbn. reflexivity. Qed.

Lemma combine_empty_r {S A} (m : ls_monad S A) :
  combine m empty = m.
Proof.
  revert m. fix IH 1.
  intros [m]. cbn. f_equal.
  apply functional_extensionality. intros s.
  destruct (m s) as [m' s'].
  destruct m' as [| x m'].
  - reflexivity.
  - rewrite -> (IH m').
    reflexivity.
Qed.

Lemma combine_assoc {S A} (m1 m2 m3 : ls_monad S A) :
  combine (combine m1 m2) m3 = combine m1 (combine m2 m3).
Proof.
  revert m1 m2. fix IH 1.
  intros [m1] m2. cbn. f_equal.
  apply functional_extensionality. intros s.
  destruct (m1 s) as [m1' s'].
  destruct m1' as [| x m1'].
  - destruct m2 as [m2]. cbn.
    reflexivity.
  - rewrite -> (IH m1' m2).
    reflexivity.
Qed.

Lemma map_combine_distr {S A B} (f : A -> B) (m1 m2 : ls_monad S A) :
  combine (map f m1) (map f m2) = map f (combine m1 m2).
Proof.
  revert m1 m2. fix IH 1.
  intros [m1] m2. cbn. f_equal.
  apply functional_extensionality. intros s.
  destruct (m1 s) as [m1' s'].
  destruct m1' as [| x m1'].
  - destruct m2 as [m2]. cbn.
    reflexivity.
  - rewrite -> (IH m1' m2).
    reflexivity.
Qed.

Lemma apply_combine_distr_r {S A B} (m1 m2 : ls_monad S (A -> B)) (m3 : ls_monad S A) :
  combine (apply m1 m3) (apply m2 m3) = apply (combine m1 m2) m3.
Proof.
  revert m1 m2. fix IH 1.
  intros [m1] m2. cbn. f_equal.
  apply functional_extensionality. intros s.
  destruct (m1 s) as [m1' s'].
  destruct m1' as [| f m1'].
  - destruct m2 as [m2]. cbn.
    reflexivity.
  - rewrite <- (IH m1' m2).
    rewrite <- combine_assoc.
    destruct (combine (map f m3) (apply m1' m3)) as [m]. cbn.
    reflexivity.
Qed.

Lemma bind_combine_distr {S A B} (m1 m2 : ls_monad S A) (f : A -> ls_monad S B) :
  combine (bind m1 f) (bind m2 f) = bind (combine m1 m2) f.
Proof.
  revert m1 m2. fix IH 1.
  intros [m1] m2. cbn. f_equal.
  apply functional_extensionality. intros s.
  destruct (m1 s) as [m1' s'].
  destruct m1' as [| x m1'].
  - destruct m2 as [m2]. cbn.
    reflexivity.
  - rewrite <- (IH m1' m2).
    rewrite <- combine_assoc.
    destruct (combine (f x) (bind m1' f)) as [m]. cbn.
    reflexivity.
Qed.

Lemma empty_bind {S A B} (f : A -> ls_monad S B) :
  bind empty f = empty.
Proof. cbn. reflexivity. Qed.

Lemma pure_bind {S A B} (x : A) (f : A -> ls_monad S B) :
  bind (pure x) f = f x.
Proof.
  cbn. fold (@empty S B).
  rewrite -> combine_empty_r.
  destruct (f x) as [m]. cbn.
  reflexivity.
Qed.

Lemma bind_pure {S A} (m : ls_monad S A) :
  bind m pure = m.
Proof.
  revert m. fix IH 1.
  intros [m]. cbn. f_equal.
  apply functional_extensionality. intros s.
  destruct (m s) as [m' s'].
  destruct m' as [| x m'].
  - reflexivity.
  - rewrite -> (IH m').
    destruct m' as [m']. cbn.
    reflexivity.
Qed.

Lemma bind_assoc {S A B C} (m : ls_monad S A) (f : A -> ls_monad S B) (g : B -> ls_monad S C) :
  bind (bind m f) g = bind m (fun x => bind (f x) g).
Proof.
  revert m. fix IH 1.
  intros [m]. cbn. f_equal.
  apply functional_extensionality. intros s.
  destruct (m s) as [m' s'].
  destruct m' as [| x m'].
  - reflexivity.
  - rewrite <- (IH m').
    rewrite -> bind_combine_distr.
    destruct (combine (f x) (bind m' f)) as [m'']. cbn.
    reflexivity.
Qed.
