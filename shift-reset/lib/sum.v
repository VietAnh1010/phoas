Definition map {E A B} (f : A -> B) (s : E + A) : E + B :=
  match s with
  | inl e => inl e
  | inr x => inr (f x)
  end.

Definition pure {E A} : A -> E + A := inr.

Definition bind {E A B} (s : E + A) (f : A -> E + B) : E + B :=
  match s with
  | inl e => inl e
  | inr x => f x
  end.

Definition fold {E A B} (f : E -> B) (g : A -> B) (s : E + A) : B :=
  match s with
  | inl e => f e
  | inr x => g x
  end.

Lemma eq_dec :
  forall {E A : Type}
         (E_eq_dec : forall (x y : E), {x = y} + {x <> y})
         (A_eq_dec : forall (x y : A), {x = y} + {x <> y})
         (s1 s2 : E + A),
    {s1 = s2} + {s1 <> s2}.
Proof. decide equality. Defined.
