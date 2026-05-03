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
  map (fun x => f (g x)) m = map f (map g m).
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
Proof. cbv. destruct m as [m]. reflexivity. Qed.

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

Lemma map_combine_distr {R A B} (f : A -> B) (m1 m2 : lr_monad R A) :
  map f (combine m1 m2) = combine (map f m1) (map f m2).
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

Lemma apply_combine_distr {R A B} (m1 m2 : lr_monad R (A -> B)) (m3 : lr_monad R A) :
  apply (combine m1 m2) m3 = combine (apply m1 m3) (apply m2 m3).
Proof.
  revert m1 m2. fix IH 1.
  intros [m1] m2. cbn. f_equal.
  apply functional_extensionality. intros r.
  destruct (m1 r) as [| f m1'].
  - destruct m2 as [m2]. cbn.
    reflexivity.
  - rewrite -> (IH m1' m2).
    rewrite <- combine_assoc.
    destruct (combine (map f m3) (apply m1' m3)) as [m]. cbn.
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

Lemma bind_empty {R A B} (f : A -> lr_monad R B) :
  bind empty f = empty.
Proof. cbv. reflexivity. Qed.

Lemma seq_right_empty {R A B} (m : lr_monad R A) :
  seq_right m (@empty R B) = empty.
Proof.
  revert m. fix IH 1.
  intros [m]. cbn.
  unfold empty at 2. f_equal.
  apply functional_extensionality. intros r.
  destruct (m r) as [| _ m'].
  - reflexivity.
  - rewrite -> (IH m'). cbn.
    reflexivity.
Qed.

Lemma map_pure {R A B} (f : A -> B) (x : A) :
  map f (@pure R A x) = pure (f x).
Proof. cbv. reflexivity. Qed.

Lemma apply_pure_l {R A B} (f : A -> B) (m : lr_monad R A) :
  apply (pure f) m = map f m.
Proof.
  cbn. fold (@empty R B).
  rewrite -> combine_empty_r.
  destruct (map f m) as [m']. cbn.
  reflexivity.
Qed.

Lemma apply_pure_r {R A B} (m : lr_monad R (A -> B)) (x : A) :
  apply m (pure x) = map (fun f => f x) m.
Proof.
  revert m. fix IH 1.
  intros [m]. cbn. f_equal.
  apply functional_extensionality. intros r.
  destruct (m r) as [| f m'].
  - reflexivity.
  - rewrite -> (IH m').
    destruct (map (fun f => f x) m') as [m'']. cbn.
    reflexivity.
Qed.

Lemma map_apply {R A B C} (f : B -> C) (m1 : lr_monad R (A -> B)) (m2 : lr_monad R A) :
  map f (apply m1 m2) = apply (map (fun g x => f (g x)) m1) m2.
Proof.
  revert m1. fix IH 1.
  intros [m1]. cbn. f_equal.
  apply functional_extensionality. intros r.
  destruct (m1 r) as [| g m1'].
  - reflexivity.
  - rewrite <- (IH m1').
    rewrite -> (map_comp f g).
    rewrite <- map_combine_distr.
    destruct (combine (map g m2) (apply m1' m2)) as [m]. cbn.
    reflexivity.
Qed.

Lemma apply_assoc {R A B C} (m1 : lr_monad R (B -> C)) (m2 : lr_monad R (A -> B)) (m3 : lr_monad R A) :
  apply m1 (apply m2 m3) = apply (apply (map (fun f g x => f (g x)) m1) m2) m3.
Proof.
  revert m1. fix IH 1.
  intros [m1]. cbn. f_equal.
  apply functional_extensionality. intros r.
  destruct (m1 r) as [| f m1'].
  - reflexivity.
  - rewrite -> (IH m1').
    rewrite -> map_apply.
    rewrite <- apply_combine_distr.
    destruct (combine (map (fun g x => f (g x)) m2) (apply (map (fun f g x => f (g x)) m1') m2)) as [m]. cbn.
    reflexivity.
Qed.

Lemma bind_pure_l {R A B} (x : A) (f : A -> lr_monad R B) :
  bind (pure x) f = f x.
Proof.
  cbn. fold (@empty R B).
  rewrite -> combine_empty_r.
  destruct (f x) as [m]. cbn.
  reflexivity.
Qed.

Lemma bind_pure_r {R A} (m : lr_monad R A) :
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

Lemma bind_map {R A B} (m1 : lr_monad R (A -> B)) (m2 : lr_monad R A) :
  bind m1 (fun f => map f m2) = apply m1 m2.
Proof.
  revert m1. fix IH 1.
  intros [m]. cbn. f_equal.
  apply functional_extensionality. intros r.
  destruct (m r) as [| x m'].
  - reflexivity.
  - rewrite -> (IH m').
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
    rewrite <- bind_combine_distr.
    destruct (combine (f x) (bind m' f)) as [m'']. cbn.
    reflexivity.
Qed.
