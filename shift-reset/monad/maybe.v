Record maybe (A : Type) : Type := Maybe { run_maybe : option A }.
Definition t : Type -> Type := maybe.

Arguments Maybe {A} _.
Arguments run_maybe {A} _.

Definition pure {A} (x : A) : maybe A :=
  Maybe (Some x).

Definition map {A B} (f : A -> B) (m : maybe A) : maybe B :=
  Maybe match run_maybe m with
    | None => None
    | Some x => Some (f x)
    end.

Definition mapl {A B} (x : B) (m : maybe A) : maybe B :=
  Maybe match run_maybe m with
    | None => None
    | Some _ => Some x
    end.

Definition app {A B} (m1 : maybe (A -> B)) (m2 : maybe A) : maybe B :=
  Maybe match run_maybe m1 with
    | None => None
    | Some f =>
        match run_maybe m2 with
        | None => None
        | Some x => Some (f x)
        end
    end.

Definition appl {A B} (m1 : maybe A) (m2 : maybe B) : maybe A :=
  Maybe match run_maybe m1 with
    | None => None
    | Some x =>
        match run_maybe m2 with
        | None => None
        | Some _ => Some x
        end
    end.

Definition appr {A B} (m1 : maybe A) (m2 : maybe B) : maybe B :=
  match run_maybe m1 with
  | None => Maybe None
  | Some _ => m2
  end.

Definition bind {A B} (m : maybe A) (f : A -> maybe B) : maybe B :=
  match run_maybe m with
  | None => Maybe None
  | Some x => f x
  end.

Definition join {A} (m : maybe (maybe A)) : maybe A :=
  match run_maybe m with
  | None => Maybe None
  | Some m => m
  end.

Definition empty {A} : maybe A :=
  Maybe None.

Definition alt {A} (m1 : maybe A) (m2 : maybe A) : maybe A :=
  match run_maybe m1 with
  | None => m2
  | Some x => Maybe (Some x)
  end.

Definition map_maybe {A B} (f : option A -> option B) (m : maybe A) : maybe B :=
  Maybe (f (run_maybe m)).

Module MaybeNotations.
  Declare Scope maybe_scope.
  Delimit Scope maybe_scope with maybe.
  Bind Scope maybe_scope with maybe.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : maybe_scope.
  Notation "x <$ m" := (mapl x m) (at level 65, right associativity) : maybe_scope.
  Notation "m1 <*> m2" := (app m1 m2) (at level 55, left associativity) : maybe_scope.
  Notation "m1 <* m2" := (appl m1 m2) (at level 55, left associativity) : maybe_scope.
  Notation "m1 *> m2" := (appr m1 m2) (at level 55, left associativity) : maybe_scope.
  Notation "m1 <|> m2" := (alt m1 m2) (at level 55, left associativity) : maybe_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : maybe_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : maybe_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : maybe_scope.
End MaybeNotations.
