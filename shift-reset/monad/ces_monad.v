Record ces_monad (R E S A : Type) : Type := CESMonad { run_ces_monad : (A -> S -> (E + R) * S) -> S -> (E + R) * S }.
Definition t : Type -> Type -> Type -> Type -> Type := ces_monad.

Arguments CESMonad {R E S A} _.
Arguments run_ces_monad {R E S A} _ _ _.

Definition pure {R E S A} (x : A) : ces_monad R E S A :=
  CESMonad (fun k => k x).

Definition map {R E S A B} (f : A -> B) (m : ces_monad R E S A) : ces_monad R E S B :=
  CESMonad (fun k => run_ces_monad m (fun x => k (f x))).

Definition mapl {R E S A B} (x : B) (m : ces_monad R E S A) : ces_monad R E S B :=
  CESMonad (fun k => run_ces_monad m (fun _ => k x)).

Definition app {R E S A B} (m1 : ces_monad R E S (A -> B)) (m2 : ces_monad R E S A) : ces_monad R E S B :=
  CESMonad (fun k => run_ces_monad m1 (fun f => run_ces_monad m2 (fun x => k (f x)))).

Definition appl {R E S A B} (m1 : ces_monad R E S A) (m2 : ces_monad R E S B) : ces_monad R E S A :=
  CESMonad (fun k => run_ces_monad m1 (fun x => run_ces_monad m2 (fun _ => k x))).

Definition appr {R E S A B} (m1 : ces_monad R E S A) (m2 : ces_monad R E S B) : ces_monad R E S B :=
  CESMonad (fun k => run_ces_monad m1 (fun _ => run_ces_monad m2 k)).

Definition bind {R E S A B} (m : ces_monad R E S A) (f : A -> ces_monad R E S B) : ces_monad R E S B :=
  CESMonad (fun k => run_ces_monad m (fun x => run_ces_monad (f x) k)).

Definition join {R E S A} (m : ces_monad R E S (ces_monad R E S A)) : ces_monad R E S A :=
  CESMonad (fun k => run_ces_monad m (fun m => run_ces_monad m k)).

Definition callcc {R E S A B} (f : (A -> ces_monad R E S B) -> ces_monad R E S A) : ces_monad R E S A :=
  CESMonad (fun k => run_ces_monad (f (fun x => CESMonad (fun _ => k x))) k).

Definition reset {R R' E S} (m : ces_monad R E S R) : ces_monad R' E S R :=
  CESMonad
    (fun k s =>
       let (m, s) := run_ces_monad m (fun x s => (inr x, s)) s in
       match m with
       | inl e => (inl e, s)
       | inr x => k x s
       end).

Definition shift {R R' E S A} (f : (A -> ces_monad R' E S R) -> ces_monad R E S R) : ces_monad R E S A :=
  CESMonad
    (fun k s =>
       run_ces_monad
         (f
            (fun x =>
               CESMonad
                 (fun k' s =>
                    let (m, s) := k x s in
                    match m with
                    | inl e => (inl e, s)
                    | inr y => k' y s
                    end)))
         (fun x s => (inr x, s)) s).

Definition throw {R E S A} (e : E) : ces_monad R E S A :=
  CESMonad (fun _ s => (inl e, s)).

Definition except {R E S A} (m : E + A) : ces_monad R E S A :=
  CESMonad
    (fun k s =>
       match m with
       | inl e => (inl e, s)
       | inr x => k x s
       end).

Definition get {R E S} : ces_monad R E S S :=
  CESMonad (fun k s => k s s).

Definition put {R E S} (s : S) : ces_monad R E S unit :=
  CESMonad (fun k _ => k tt s).

Definition state {R E S A} (f : S -> A * S) : ces_monad R E S A :=
  CESMonad (fun k s => let (x, s) := f s in k x s).

Definition gets {R E S A} (f : S -> A) : ces_monad R E S A :=
  CESMonad (fun k s => k (f s) s).

Definition modify {R E S} (f : S -> S) : ces_monad R E S unit :=
  CESMonad (fun k s => k tt (f s)).

Definition map_cont {R E S A} (f : R -> R) (m : ces_monad R E S A) : ces_monad R E S A :=
  CESMonad
    (fun k s =>
       let (m, s) := run_ces_monad m k s in
       match m with
       | inl e => (inl e, s)
       | inr x => (inr (f x), s)
       end).

Definition map_state {R E S A B} (f : A * S -> B * S) (m : ces_monad R E S A) : ces_monad R E S B :=
  CESMonad (fun k s => run_ces_monad m (fun x s => let (y, s) := f (x, s) in k y s) s).

Definition with_state {R E S A} (f : S -> S) (m : ces_monad R E S A) : ces_monad R E S A :=
  CESMonad (fun k s => run_ces_monad m k (f s)).

Module CESMonadNotations.
  Declare Scope ces_monad_scope.
  Delimit Scope ces_monad_scope with ces_monad.
  Bind Scope ces_monad_scope with ces_monad.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : ces_monad_scope.
  Notation "x <$ m" := (mapl x m) (at level 65, right associativity) : ces_monad_scope.
  Notation "m1 <*> m2" := (app m1 m2) (at level 55, left associativity) : ces_monad_scope.
  Notation "m1 <* m2" := (appl m1 m2) (at level 55, left associativity) : ces_monad_scope.
  Notation "m1 *> m2" := (appr m1 m2) (at level 55, left associativity) : ces_monad_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : ces_monad_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : ces_monad_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : ces_monad_scope.
End CESMonadNotations.
