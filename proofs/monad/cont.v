From shift_reset.monad Require Import cont.

Lemma map_id {R A} (m : cont R A) :
  map (fun x => x) m = m.
Proof. cbv. destruct m as [m]. reflexivity. Qed.

Lemma map_comp {R A B C} (f : B -> C) (g : A -> B) (m : cont R A) :
  map f (map g m) = map (fun x => f (g x)) m.
Proof. cbv. reflexivity. Qed.

Lemma pure_bind {R A B} (x : A) (f : A -> cont R B) :
  bind (pure x) f = f x.
Proof. cbv. destruct (f x) as [m]. reflexivity. Qed.

Lemma bind_pure {R A} (m : cont R A) :
  bind m pure = m.
Proof. cbv. destruct m as [m]. reflexivity. Qed.

Lemma bind_assoc {R A B C} (m : cont R A) (f : A -> cont R B) (g : B -> cont R C) :
  bind (bind m f) g = bind m (fun x => bind (f x) g).
Proof. cbv. reflexivity. Qed.

Lemma reset_idemp {R R'} (m : cont R R) :
  @reset R R' (reset m) = @reset R R' m.
Proof. cbv. reflexivity. Qed.
