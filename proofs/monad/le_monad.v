From shift_reset.monad Require Import le_monad.

Lemma map_id {E A} (m : le_monad E A) :
  map (fun x => x) m = m.
Proof.
  revert m. fix IH 1.
  intros [m]. cbn. f_equal.
  destruct m as [e | m].
  - reflexivity.
  - destruct m as [| x m'].
    + reflexivity.
    + rewrite -> (IH m').
      reflexivity.
Qed.

Lemma map_comp {E A B C} (f : B -> C) (g : A -> B) (m : le_monad E A) :
  map (fun x => f (g x)) m = map f (map g m).
Proof.
  revert m. fix IH 1.
  intros [m]. cbn. f_equal.
  destruct m as [e | m].
  - reflexivity.
  - destruct m as [| x m'].
    + reflexivity.
    + rewrite -> (IH m').
      reflexivity.
Qed.

Lemma combine_empty_l {E A} (m : le_monad E A) :
  combine empty m = m.
Proof. cbv. destruct m as [m]. reflexivity. Qed.

Lemma combine_empty_r {E A} (m : le_monad E A) :
  combine m empty = m.
Proof.
  revert m. fix IH 1.
  intros [m]. cbn. f_equal.
  destruct m as [e | m].
  - reflexivity.
  - destruct m as [| x m'].
    + reflexivity.
    + rewrite -> (IH m').
      reflexivity.
Qed.

Lemma combine_assoc {E A} (m1 m2 m3 : le_monad E A) :
  combine (combine m1 m2) m3 = combine m1 (combine m2 m3).
Proof.
  revert m1 m2. fix IH 1.
  intros [m1] m2. cbn. f_equal.
  destruct m1 as [e | m].
  - reflexivity.
  - destruct m as [| x m1'].
    + destruct m2 as [m2]. cbn.
      reflexivity.
    + rewrite -> (IH m1' m2).
      reflexivity.
Qed.

Lemma map_combine_distr {E A B} (f : A -> B) (m1 m2 : le_monad E A) :
  map f (combine m1 m2) = combine (map f m1) (map f m2).
Proof.
  revert m1 m2. fix IH 1.
  intros [m1] m2. cbn. f_equal.
  destruct m1 as [e | m].
  - reflexivity.
  - destruct m as [| x m1'].
    + destruct m2 as [m2]. cbn.
      reflexivity.
    + rewrite -> (IH m1' m2).
      reflexivity.
Qed.

Lemma apply_combine_distr {E A B} (m1 m2 : le_monad E (A -> B)) (m3 : le_monad E A) :
  apply (combine m1 m2) m3 = combine (apply m1 m3) (apply m2 m3).
Proof.
  revert m1 m2. fix IH 1.
  intros [m1] m2. cbn. f_equal.
  destruct m1 as [e | m].
  - reflexivity.
  - destruct m as [| f m1'].
    + destruct m2 as [m2]. cbn.
      reflexivity.
    + rewrite -> (IH m1' m2).
      rewrite <- combine_assoc.
      destruct (combine (map f m3) (apply m1' m3)) as [m]. cbn.
      reflexivity.
Qed.

Lemma bind_combine_distr {E A B} (m1 m2 : le_monad E A) (f : A -> le_monad E B) :
  bind (combine m1 m2) f = combine (bind m1 f) (bind m2 f).
Proof.
  revert m1 m2. fix IH 1.
  intros [m1] m2. cbn. f_equal.
  destruct m1 as [e | m].
  - reflexivity.
  - destruct m as [| x m1'].
    + destruct m2 as [m2]. cbn.
      reflexivity.
    + rewrite -> (IH m1' m2).
      rewrite <- combine_assoc.
      destruct (combine (f x) (bind m1' f)) as [m]. cbn.
      reflexivity.
Qed.

Lemma map_empty {E A B} (f : A -> B) :
  map f (@empty E A) = empty.
Proof. cbv. reflexivity. Qed.

Lemma apply_empty {E A B} (m : le_monad E A) :
  apply (@empty E (A -> B)) m = empty.
Proof. cbv. reflexivity. Qed.

Lemma bind_empty {E A B} (f : A -> le_monad E B) :
  bind empty f = empty.
Proof. cbv. reflexivity. Qed.

Lemma map_pure {E A B} (f : A -> B) (x : A) :
  map f (@pure E A x) = pure (f x).
Proof. cbv. reflexivity. Qed.

Lemma apply_pure_l {E A B} (f : A -> B) (m : le_monad E A) :
  apply (pure f) m = map f m.
Proof.
  cbn. fold (@empty E B).
  rewrite -> combine_empty_r.
  destruct (map f m) as [m']. cbn.
  reflexivity.
Qed.

Lemma apply_pure_r {E A B} (m : le_monad E (A -> B)) (x : A) :
  apply m (pure x) = map (fun f => f x) m.
Proof.
  revert m. fix IH 1.
  intros [m]. cbn. f_equal.
  destruct m as [e | m].
  - reflexivity.
  - destruct m as [| f m'].
    + reflexivity.
    + rewrite -> (IH m').
      destruct (map (fun f => f x) m') as [m'']. cbn.
      reflexivity.
Qed.

Lemma map_apply {E A B C} (f : B -> C) (m1 : le_monad E (A -> B)) (m2 : le_monad E A) :
  map f (apply m1 m2) = apply (map (fun g x => f (g x)) m1) m2.
Proof.
  revert m1. fix IH 1.
  intros [m1]. cbn. f_equal.
  destruct m1 as [e | m].
  - reflexivity.
  - destruct m as [| g m1'].
    + reflexivity.
    + rewrite <- (IH m1').
      rewrite -> (map_comp f g).
      rewrite <- map_combine_distr.
      destruct (combine (map g m2) (apply m1' m2)) as [m]. cbn.
      reflexivity.
Qed.

Lemma apply_assoc {E A B C} (m1 : le_monad E (B -> C)) (m2 : le_monad E (A -> B)) (m3 : le_monad E A) :
  apply m1 (apply m2 m3) = apply (apply (map (fun f g x => f (g x)) m1) m2) m3.
Proof.
  revert m1. fix IH 1.
  intros [m1]. cbn. f_equal.
  destruct m1 as [e | m].
  - reflexivity.
  - destruct m as [| f m1'].
    + reflexivity.
    + rewrite -> (IH m1').
      rewrite -> map_apply.
      rewrite <- apply_combine_distr.
      destruct (combine (map (fun g x => f (g x)) m2) (apply (map (fun f g x => f (g x)) m1') m2)) as [m]. cbn.
      reflexivity.
Qed.

Lemma bind_pure_l {E A B} (x : A) (f : A -> le_monad E B) :
  bind (pure x) f = f x.
Proof.
  cbn. fold (@empty E B).
  rewrite -> combine_empty_r.
  destruct (f x) as [m]. cbn.
  reflexivity.
Qed.

Lemma bind_pure_r {E A} (m : le_monad E A) :
  bind m pure = m.
Proof.
  revert m. fix IH 1.
  intros [m]. cbn. f_equal.
  destruct m as [e | m].
  - reflexivity.
  - destruct m as [| x m'].
    + reflexivity.
    + rewrite -> (IH m').
      destruct m' as [m']. cbn.
      reflexivity.
Qed.

Lemma bind_map {E A B} (m1 : le_monad E (A -> B)) (m2 : le_monad E A) :
  bind m1 (fun f => map f m2) = apply m1 m2.
Proof.
  revert m1. fix IH 1.
  intros [m]. cbn. f_equal.
  destruct m as [e | m].
  - reflexivity.
  - destruct m as [| x m'].
    + reflexivity.
    + rewrite -> (IH m').
      reflexivity.
Qed.

Lemma bind_assoc {E A B C} (m : le_monad E A) (f : A -> le_monad E B) (g : B -> le_monad E C) :
  bind (bind m f) g = bind m (fun x => bind (f x) g).
Proof.
  revert m. fix IH 1.
  intros [m]. cbn. f_equal.
  destruct m as [e | m].
  - reflexivity.
  - destruct m as [| x m'].
    + reflexivity.
    + rewrite <- (IH m').
      rewrite <- bind_combine_distr.
      destruct (combine (f x) (bind m' f)) as [m'']. cbn.
      reflexivity.
Qed.
