Record identity (A : Type) : Type := Identity { run_identity : A }.
Definition t : Type -> Type := identity.

Arguments Identity {A} _.
Arguments run_identity {A} _.

Definition pure {A} : A -> identity A := Identity.

Definition map {A B} (f : A -> B) (m : identity A) : identity B :=
  Identity (f (run_identity m)).

Definition mapl {A B} (x : B) (_ : identity A) : identity B :=
  Identity x.

Definition app {A B} (m1 : identity (A -> B)) (m2 : identity A) : identity B :=
  Identity (run_identity m1 (run_identity m2)).

Definition appl {A B} (m : identity A) (_ : identity B) : identity A := m.
Definition appr {A B} (_ : identity A) (m : identity B) : identity B := m.

Definition bind {A B} (m : identity A) (f : A -> identity B) : identity B :=
  f (run_identity m).

Definition join {A} : identity (identity A) -> identity A := run_identity.

Module IdentityNotations.
  Declare Scope identity_scope.
  Delimit Scope identity_scope with identity.
  Bind Scope identity_scope with identity.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : identity_scope.
  Notation "x <$ m" := (mapl x m) (at level 65, right associativity) : identity_scope.
  Notation "m1 <*> m2" := (app m1 m2) (at level 55, left associativity) : identity_scope.
  Notation "m1 <* m2" := (appl m1 m2) (at level 55, left associativity) : identity_scope.
  Notation "m1 *> m2" := (appr m1 m2) (at level 55, left associativity) : identity_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : identity_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : identity_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : identity_scope.
End IdentityNotations.
