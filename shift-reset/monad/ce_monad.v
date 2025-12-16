Record ce_monad (R E A : Type) : Type := CEMonad { run_ce_monad : (A -> E + R) -> E + R }.
Definition t : Type -> Type -> Type -> Type := ce_monad.

Arguments CEMonad {R E A} _.
Arguments run_ce_monad {R E A} _ _.

Definition pure {R E A} (x : A) : ce_monad R E A :=
  CEMonad (fun k => k x).

Definition map {R E A B} (f : A -> B) (m : ce_monad R E A) : ce_monad R E B :=
  CEMonad (fun k => run_ce_monad m (fun x => k (f x))).

Definition mapl {R E A B} (x : B) (m : ce_monad R E A) : ce_monad R E B :=
  CEMonad (fun k => run_ce_monad m (fun _ => k x)).

Definition app {R E A B} (m1 : ce_monad R E (A -> B)) (m2 : ce_monad R E A) : ce_monad R E B :=
  CEMonad (fun k => run_ce_monad m1 (fun f => run_ce_monad m2 (fun x => k (f x)))).

Definition appl {R E A B} (m1 : ce_monad R E A) (m2 : ce_monad R E B) : ce_monad R E A :=
  CEMonad (fun k => run_ce_monad m1 (fun x => run_ce_monad m2 (fun _ => k x))).

Definition appr {R E A B} (m1 : ce_monad R E A) (m2 : ce_monad R E B) : ce_monad R E B :=
  CEMonad (fun k => run_ce_monad m1 (fun _ => run_ce_monad m2 k)).

Definition bind {R E A B} (m : ce_monad R E A) (f : A -> ce_monad R E B) : ce_monad R E B :=
  CEMonad (fun k => run_ce_monad m (fun x => run_ce_monad (f x) k)).

Definition join {R E A} (m : ce_monad R E (ce_monad R E A)) : ce_monad R E A :=
  CEMonad (fun k => run_ce_monad m (fun m => run_ce_monad m k)).

Definition callcc {R E A B} (f : (A -> ce_monad R E B) -> ce_monad R E A) : ce_monad R E A :=
  CEMonad (fun k => run_ce_monad (f (fun x => CEMonad (fun _ => k x))) k).

Definition reset {R R' E} (m : ce_monad R E R) : ce_monad R' E R :=
  CEMonad
    (fun k =>
       match run_ce_monad m inr with
       | inl e => inl e
       | inr x => k x
       end).

Definition shift {R R' E A} (f : (A -> ce_monad R' E R) -> ce_monad R E R) : ce_monad R E A :=
  CEMonad
    (fun k =>
       run_ce_monad
         (f (fun x =>
               CEMonad
                 (fun k' =>
                    match k x with
                    | inl e => inl e
                    | inr y => k' y
                    end)))
         inr).

Definition throw {R E A} (e : E) : ce_monad R E A :=
  CEMonad (fun _ => inl e).

Definition except {R E A} (m : E + A) : ce_monad R E A :=
  CEMonad
    (fun k =>
       match m with
       | inl e => inl e
       | inr x => k x
       end).

Definition map_cont {R E A} (f : R -> R) (m : ce_monad R E A) : ce_monad R E A :=
  CEMonad
    (fun k =>
       match run_ce_monad m k with
       | inl e => inl e
       | inr x => inr (f x)
       end).

Module CEMonadNotations.
  Declare Scope ce_monad_scope.
  Delimit Scope ce_monad_scope with ce_monad.
  Bind Scope ce_monad_scope with ce_monad.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : ce_monad_scope.
  Notation "x <$ m" := (mapl x m) (at level 65, right associativity) : ce_monad_scope.
  Notation "m1 <*> m2" := (app m1 m2) (at level 55, left associativity) : ce_monad_scope.
  Notation "m1 <* m2" := (appl m1 m2) (at level 55, left associativity) : ce_monad_scope.
  Notation "m1 *> m2" := (appr m1 m2) (at level 55, left associativity) : ce_monad_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : ce_monad_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : ce_monad_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : ce_monad_scope.
End CEMonadNotations.
