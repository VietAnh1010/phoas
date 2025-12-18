Definition map {A B} (f : A -> B) (o : option A) : option B :=
  match o with
  | None => None
  | Some x => Some (f x)
  end.

Definition pure {A} : A -> option A := Some.

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
