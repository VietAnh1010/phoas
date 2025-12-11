Record except (E A : Type) : Type := Except { run_except : E + A }.
Definition t : Type -> Type -> Type := except.

Arguments Except {E A} _.
Arguments run_except {E A} _.

Definition map {E A B} (f : A -> B) (m : except E A) : except E B :=
  Except match run_except m with
    | inl e => inl e
    | inr x => inr (f x)
    end.

Definition mapl {E A B} (x : B) (m : except E A) : except E B :=
  Except match run_except m with
    | inl e => inl e
    | inr _ => inr x
    end.

Definition pure {E A} (x : A) : except E A :=
  Except (inr x).

Definition app {E A B} (m1 : except E (A -> B)) (m2 : except E A) : except E B :=
  Except match run_except m1 with
    | inl e => inl e
    | inr f =>
        match run_except m2 with
        | inl e => inl e
        | inr x => inr (f x)
        end
    end.

Definition appl {E A B} (m1 : except E A) (m2 : except E B) : except E A :=
  Except match run_except m1 with
    | inl e => inl e
    | inr x =>
        match run_except m2 with
        | inl e => inl e
        | inr _ => inr x
        end
    end.

Definition appr {E A B} (m1 : except E A) (m2 : except E B) : except E B :=
  Except match run_except m1 with
    | inl e => inl e
    | inr _ => run_except m2
    end.

Definition bind {E A B} (m : except E A) (f : A -> except E B) : except E B :=
  Except match run_except m with
    | inl e => inl e
    | inr x => run_except (f x)
    end.

Definition throw {E A} (e : E) : except E A :=
  Except (inl e).

Definition catch {E A} (m : except E A) (f : E -> except E A) : except E A :=
  Except match run_except m with
    | inl e => run_except (f e)
    | inr x => inr x
    end.

Module ExceptNotations.
  Declare Scope except_scope.
  Delimit Scope except_scope with except.
  Bind Scope except_scope with except.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : except_scope.
  Notation "x <$ m" := (mapl x m) (at level 65, right associativity) : except_scope.
  Notation "m1 <*> m2" := (app m1 m2) (at level 55, left associativity) : except_scope.
  Notation "m1 <* m2" := (appl m1 m2) (at level 55, left associativity) : except_scope.
  Notation "m1 *> m2" := (appr m1 m2) (at level 55, left associativity) : except_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : except_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : except_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : except_scope.
End ExceptNotations.
