Definition bind {A B} (o : option A) (f : A -> option B) : option B :=
  match o with
  | None => None
  | Some x => f x
  end.
