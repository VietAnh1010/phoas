From shift_reset.monad Require Import reader.

Lemma map_id {R A} (m : reader R A) :
  map (fun x => x) m = m.
Proof. cbv. destruct m as [m]. reflexivity. Qed.

Lemma map_comp {R A B C} (f : B -> C) (g : A -> B) (m : reader R A) :
  map (fun x => f (g x)) m = map f (map g m).
Proof. cbv. reflexivity. Qed.

Lemma bind_pure_l {R A B} (x : A) (f : A -> reader R B) :
  bind (pure x) f = f x.
Proof. cbv. destruct (f x) as [m]. reflexivity. Qed.

Lemma bind_pure_r {R A} (m : reader R A) :
  bind m pure = m.
Proof. cbv. destruct m as [m]. reflexivity. Qed.

Lemma bind_assoc {R A B C} (m : reader R A) (f : A -> reader R B) (g : B -> reader R C) :
  bind (bind m f) g = bind m (fun x => bind (f x) g).
Proof. cbv. reflexivity. Qed.
