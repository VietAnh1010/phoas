Record ec_monad (E R A : Type) : Type := ECMonad { run_ec_monad : (E -> R) -> (A -> R) -> R }.
Definition t : Type -> Type -> Type -> Type := ec_monad.

Arguments ECMonad {E R A} _.
Arguments run_ec_monad {E R A} _ _ _.

Definition pure {E R A} (x : A) : ec_monad E R A :=
  ECMonad (fun _ k => k x).

Definition map {E R A B} (f : A -> B) (m : ec_monad E R A) : ec_monad E R B :=
  ECMonad (fun h k => run_ec_monad m h (fun x => k (f x))).

Definition mapl {E R A B} (x : B) (m : ec_monad E R A) : ec_monad E R B :=
  ECMonad (fun h k => run_ec_monad m h (fun _ => k x)).

Definition app {E R A B} (m1 : ec_monad E R (A -> B)) (m2 : ec_monad E R A) : ec_monad E R B :=
  ECMonad (fun h k => run_ec_monad m1 h (fun f => run_ec_monad m2 h (fun x => k (f x)))).

Definition appl {E R A B} (m1 : ec_monad E R A) (m2 : ec_monad E R B) : ec_monad E R A :=
  ECMonad (fun h k => run_ec_monad m1 h (fun x => run_ec_monad m2 h (fun _ => k x))).

Definition appr {E R A B} (m1 : ec_monad E R A) (m2 : ec_monad E R B) : ec_monad E R B :=
  ECMonad (fun h k => run_ec_monad m1 h (fun _ => run_ec_monad m2 h k)).

Definition bind {E R A B} (m : ec_monad E R A) (f : A -> ec_monad E R B) : ec_monad E R B :=
  ECMonad (fun h k => run_ec_monad m h (fun x => run_ec_monad (f x) h k)).

Definition join {E R A} (m : ec_monad E R (ec_monad E R A)) : ec_monad E R A :=
  ECMonad (fun h k => run_ec_monad m h (fun m => run_ec_monad m h k)).

Definition throw {E R A} (e : E) : ec_monad E R A :=
  ECMonad (fun h _ => h e).

Definition except {E R A} (m : E + A) : ec_monad E R A :=
  ECMonad
    (fun h k =>
       match m with
       | inl e => h e
       | inr x => k x
       end).

Definition catch {E R A} (m : ec_monad E R A) (f : E -> ec_monad E R A) : ec_monad E R A :=
  ECMonad (fun h k => run_ec_monad m (fun e => run_ec_monad (f e) h k) k).

Definition try {E R A} (m : ec_monad E R A) : ec_monad E R (E + A) :=
  ECMonad (fun _ k => run_ec_monad m (fun e => k (inl e)) (fun x => k (inr x))).

Definition finally {E R A} (m1 : ec_monad E R A) (m2 : ec_monad E R unit) : ec_monad E R A :=
  ECMonad (fun h k => run_ec_monad m1 (fun e => run_ec_monad m2 h (fun _ => h e)) (fun x => run_ec_monad m2 h (fun _ => k x))).

Definition cont {E R A} (f : (A -> R) -> R) : ec_monad E R A :=
  ECMonad (fun _ => f).

Definition callcc {E R A B} (f : (A -> ec_monad E R B) -> ec_monad E R A) : ec_monad E R A :=
  ECMonad (fun h k => run_ec_monad (f (fun x => ECMonad (fun _ _ => k x))) h k).

Definition map_except {E E' R A B} (f : E + A -> E' + B) (m : ec_monad E R A) : ec_monad E' R B :=
  ECMonad
    (fun h k =>
       run_ec_monad m
         (fun e =>
            match f (inl e) with
            | inl e => h e
            | inr x => k x
            end)
         (fun x =>
            match f (inr x) with
            | inl e => h e
            | inr y => k y
            end)).

Definition with_except {E E' R A} (f : E -> E') (m : ec_monad E R A) : ec_monad E' R A :=
  ECMonad (fun h => run_ec_monad m (fun e => h (f e))).

Definition map_cont {E R A} (f : R -> R) (m : ec_monad E R A) : ec_monad E R A :=
  ECMonad (fun h k => run_ec_monad m h (fun x => f (k x))).

Definition with_cont {E R A B} (f : (B -> R) -> A -> R) (m : ec_monad E R A) : ec_monad E R B :=
  ECMonad (fun h k => run_ec_monad m h (f k)).

Module ECMonadNotations.
  Declare Scope ec_monad_scope.
  Delimit Scope ec_monad_scope with ec_monad.
  Bind Scope ec_monad_scope with ec_monad.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : ec_monad_scope.
  Notation "x <$ m" := (mapl x m) (at level 65, right associativity) : ec_monad_scope.
  Notation "m1 <*> m2" := (app m1 m2) (at level 55, left associativity) : ec_monad_scope.
  Notation "m1 <* m2" := (appl m1 m2) (at level 55, left associativity) : ec_monad_scope.
  Notation "m1 *> m2" := (appr m1 m2) (at level 55, left associativity) : ec_monad_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : ec_monad_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : ec_monad_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : ec_monad_scope.
End ECMonadNotations.
