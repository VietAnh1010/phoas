From Stdlib Require Import FunctionalExtensionality.
From shift_reset.monad Require Import ces_monad.

Lemma bind_pure {R E S A B} (x : A) (f : A -> ces_monad R E S B) :
  bind (pure x) f = f x.
Proof. cbv. destruct (f x) as [m]. reflexivity. Qed.

Lemma pure_bind {R E S A} (m : ces_monad R E S A) :
  bind m pure = m.
Proof. cbv. destruct m as [m]. reflexivity. Qed.

Lemma bind_assoc {R E S A B C} (m : ces_monad R E S A) (f : A -> ces_monad R E S B) (g : B -> ces_monad R E S C) :
  bind (bind m f) g = bind m (fun x => bind (f x) g).
Proof. cbv. reflexivity. Qed.

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

Lemma get_put {R E S} :
  @bind R E S S unit get put = @pure R E S unit tt.
Proof. cbv. reflexivity. Qed.

Lemma put_get {R E S} (s : S) :
  @seq_right R E S unit S (put s) get = @seq_right R E S unit S (put s) (pure s).
Proof. cbv. reflexivity. Qed.

Lemma put_put {R E S} (s1 s2 : S) :
  @seq_right R E S unit unit (put s1) (put s2) = @put R E S s2.
Proof. cbv. reflexivity. Qed.
