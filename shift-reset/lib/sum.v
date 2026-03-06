Definition pure {A B} : B -> A + B := inr.

Definition map {A B C} (f : B -> C) (s : A + B) : A + C :=
  match s with
  | inl e => inl e
  | inr x => inr (f x)
  end.

Definition bind {A B C} (s : A + B) (f : B -> A + C) : A + C :=
  match s with
  | inl e => inl e
  | inr x => f x
  end.

Definition fold {A B C} (f : A -> C) (g : B -> C) (s : A + B) : C :=
  match s with
  | inl e => f e
  | inr x => g x
  end.

Lemma eq_dec :
  forall {A B : Type}
         (A_eq_dec : forall (x y : A), {x = y} + {x <> y})
         (B_eq_dec : forall (x y : B), {x = y} + {x <> y})
         (s1 s2 : A + B),
    {s1 = s2} + {s1 <> s2}.
Proof. decide equality. Defined.

Module SumNotations.
  Declare Scope sum_scope.
  Delimit Scope sum_scope with sum.
  Bind Scope sum_scope with sum.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : sum_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : sum_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : sum_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : sum_scope.
End SumNotations.
