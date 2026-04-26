From Stdlib Require Import FunctionalExtensionality.
From shift_reset.monad Require Import state.

Lemma map_id {S A} (m : state S A) :
  map (fun x => x) m = m.
Proof.
  cbv. destruct m as [m]. f_equal.
  apply functional_extensionality. intros s.
  destruct (m s) as [x s'].
  reflexivity.
Qed.

Lemma map_comp {S A B C} (f : B -> C) (g : A -> B) (m : state S A) :
  map f (map g m) = map (fun x => f (g x)) m.
Proof.
  cbv. f_equal.
  apply functional_extensionality. intros s.
  destruct m as [m].
  destruct (m s) as [x s'].
  reflexivity.
Qed.

Lemma pure_bind {S A B} (x : A) (f : A -> state S B) :
  bind (pure x) f = f x.
Proof. cbv. destruct (f x) as [m]. reflexivity. Qed.

Lemma bind_pure {S A} (m : state S A) :
  bind m pure = m.
Proof.
  cbv. destruct m as [m]. f_equal.
  apply functional_extensionality. intros s.
  destruct (m s) as [x s'].
  reflexivity.
Qed.

Lemma bind_assoc {S A B C} (m : state S A) (f : A -> state S B) (g : B -> state S C) :
  bind (bind m f) g = bind m (fun x => bind (f x) g).
Proof.
  cbv. f_equal.
  apply functional_extensionality. intros s.
  destruct m as [m].
  destruct (m s) as [x s'].
  reflexivity.
Qed.

Lemma get_put {S} :
  @bind S S unit get put = @pure S unit tt.
Proof. cbv. reflexivity. Qed.

Lemma put_get {S} (s : S) :
  seq_right (put s) get = seq_right (put s) (pure s).
Proof. cbv. reflexivity. Qed.

Lemma put_put {S} (s1 s2 : S) :
  seq_right (put s1) (put s2) = put s2.
Proof. cbv. reflexivity. Qed.
