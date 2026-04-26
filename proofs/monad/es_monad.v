From Stdlib Require Import FunctionalExtensionality.
From shift_reset.monad Require Import es_monad.

Lemma map_id {E S A} (m : es_monad E S A) :
  map (fun x => x) m = m.
Proof.
  cbv. destruct m as [m]. f_equal.
  apply functional_extensionality. intros s.
  destruct (m s) as [m' s'].
  destruct m' as [e | x].
  - reflexivity.
  - reflexivity.
Qed.

Lemma map_comp {E S A B C} (f : B -> C) (g : A -> B) (m : es_monad E S A) :
  map f (map g m) = map (fun x => f (g x)) m.
Proof.
  cbv. f_equal.
  apply functional_extensionality. intros s.
  destruct m as [m].
  destruct (m s) as [m' s'].
  destruct m' as [e | x].
  - reflexivity.
  - reflexivity.
Qed.

Lemma pure_bind {E S A B} (x : A) (f : A -> es_monad E S B) :
  bind (pure x) f = f x.
Proof. cbv. destruct (f x) as [m]. reflexivity. Qed.

Lemma bind_pure {E S A} (m : es_monad E S A) :
  bind m pure = m.
Proof.
  cbv. destruct m as [m]. f_equal.
  apply functional_extensionality. intros s.
  destruct (m s) as [m' s'].
  destruct m' as [e | x].
  - reflexivity.
  - reflexivity.
Qed.

Lemma bind_assoc {E S A B C} (m : es_monad E S A) (f : A -> es_monad E S B) (g : B -> es_monad E S C) :
  bind (bind m f) g = bind m (fun x => bind (f x) g).
Proof.
  compute. f_equal.
  apply functional_extensionality. intros s.
  destruct m as [m].
  destruct (m s) as [m' s'].
  destruct m' as [e | x].
  - reflexivity.
  - reflexivity.
Qed.

Lemma get_put {E S} :
  @bind E S S unit get put = @pure E S unit tt.
Proof. cbv. reflexivity. Qed.

Lemma put_get {E S} (s : S) :
  @seq_right E S unit S (put s) get = @seq_right E S unit S (put s) (pure s).
Proof. cbv. reflexivity. Qed.

Lemma put_put {E S} (s1 s2 : S) :
  @seq_right E S unit unit (put s1) (put s2) = @put E S s2.
Proof. cbv. reflexivity. Qed.
