From shift_reset.monad Require Import lc_monad.

Lemma map_id {R A} (m : lc_monad R A) :
  map (fun x => x) m = m.
Proof. cbv. destruct m as [m]. reflexivity. Qed.

Lemma map_comp {R A B C} (f : B -> C) (g : A -> B) (m : lc_monad R A) :
  map (fun x => f (g x)) m = map f (map g m).
Proof. cbv. reflexivity. Qed.

Lemma combine_empty_l {R A} (m : lc_monad R A) :
  combine empty m = m.
Proof. cbv. destruct m as [m]. reflexivity. Qed.

Lemma combine_empty_r {R A} (m : lc_monad R A) :
  combine m empty = m.
Proof. cbv. destruct m as [m]. reflexivity. Qed.

Lemma combine_assoc {R A} (m1 m2 m3 : lc_monad R A) :
  combine (combine m1 m2) m3 = combine m1 (combine m2 m3).
Proof. cbv. reflexivity. Qed.

Lemma map_combine_distr {R A B} (f : A -> B) (m1 m2 : lc_monad R A) :
  map f (combine m1 m2) = combine (map f m1) (map f m2).
Proof. cbv. reflexivity. Qed.

Lemma apply_combine_distr {R A B} (m1 m2 : lc_monad R (A -> B)) (m3 : lc_monad R A) :
  apply (combine m1 m2) m3 = combine (apply m1 m3) (apply m2 m3).
Proof. cbv. reflexivity. Qed.

Lemma bind_combine_distr {R A B} (m1 m2 : lc_monad R A) (f : A -> lc_monad R B) :
  bind (combine m1 m2) f = combine (bind m1 f) (bind m2 f).
Proof. cbv. reflexivity. Qed.

Lemma map_empty {R A B} (f : A -> B) :
  map f (@empty R A) = empty.
Proof. cbv. reflexivity. Qed.

Lemma apply_empty {R A B} (m : lc_monad R A) :
  apply (@empty R (A -> B)) m = empty.
Proof. cbv. reflexivity. Qed.

Lemma bind_empty {R A B} (f : A -> lc_monad R B) :
  bind empty f = empty.
Proof. cbv. reflexivity. Qed.

Lemma map_pure {R A B} (f : A -> B) (x : A) :
  map f (@pure R A x) = pure (f x).
Proof. cbv. reflexivity. Qed.

Lemma apply_pure_l {R A B} (f : A -> B) (m : lc_monad R A) :
  apply (pure f) m = map f m.
Proof. cbv. reflexivity. Qed.

Lemma apply_pure_r {R A B} (m : lc_monad R (A -> B)) (x : A) :
  apply m (pure x) = map (fun f => f x) m.
Proof. cbv. destruct m as [m]. reflexivity. Qed.

Lemma map_apply {R A B C} (f : B -> C) (m1 : lc_monad R (A -> B)) (m2 : lc_monad R A) :
  map f (apply m1 m2) = apply (map (fun g x => f (g x)) m1) m2.
Proof. cbv. reflexivity. Qed.

Lemma apply_assoc {R A B C} (m1 : lc_monad R (B -> C)) (m2 : lc_monad R (A -> B)) (m3 : lc_monad R A) :
  apply m1 (apply m2 m3) = apply (apply (map (fun f g x => f (g x)) m1) m2) m3.
Proof. cbv. reflexivity. Qed.

Lemma bind_pure_l {R A B} (x : A) (f : A -> lc_monad R B) :
  bind (pure x) f = f x.
Proof. cbv. destruct (f x) as [m]. reflexivity. Qed.

Lemma bind_pure_r {R A} (m : lc_monad R A) :
  bind m pure = m.
Proof. cbv. destruct m as [m]. reflexivity. Qed.

Lemma bind_map {R A B} (m1 : lc_monad R (A -> B)) (m2 : lc_monad R A) :
  bind m1 (fun f => map f m2) = apply m1 m2.
Proof. cbv. reflexivity. Qed.

Lemma bind_assoc {R A B C} (m : lc_monad R A) (f : A -> lc_monad R B) (g : B -> lc_monad R C) :
  bind (bind m f) g = bind m (fun x => bind (f x) g).
Proof. cbv. reflexivity. Qed.

Lemma callcc'_bind {R A B C} (m : lc_monad R A) (f : (B -> lc_monad R C) -> A -> lc_monad R B) :
  callcc' (fun k => bind m (f k)) = bind m (fun x => callcc' (fun k => f k x)).
Proof. cbv. reflexivity. Qed.
