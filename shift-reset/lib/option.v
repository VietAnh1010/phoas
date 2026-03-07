Definition pure {A} : A -> option A := Some.

Definition map {A B} (f : A -> B) (o : option A) : option B :=
  match o with
  | None => None
  | Some x => Some (f x)
  end.

Definition bind {A B} (o : option A) (f : A -> option B) : option B :=
  match o with
  | None => None
  | Some x => f x
  end.

Definition filter {A} (f : A -> bool) (o : option A) : option A :=
  match o with
  | None => None
  | Some x => if f x then o else None
  end.

Definition fold {A B} (z : B) (f : A -> B) (o : option A) : B :=
  match o with
  | None => z
  | Some x => f x
  end.

Lemma eq_dec :
  forall {A : Type}
         (A_eq_dec : forall (x y : A), {x = y} + {x <> y})
         (o1 o2 : option A),
    {o1 = o2} + {o1 <> o2}.
Proof. decide equality. Defined.

Module OptionNotations.
  Declare Scope option_scope.
  Delimit Scope option_scope with option.
  Bind Scope option_scope with option.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : option_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : option_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : option_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : option_scope.
End OptionNotations.
