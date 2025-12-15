Record esc_monad (E S R A : Type) : Type := ESCMonad { run_esc_monad : S -> (E -> S -> R) -> (A -> S -> R) -> R }.
Definition t : Type -> Type -> Type -> Type -> Type := esc_monad.

Arguments ESCMonad {E S R A} _.
Arguments run_esc_monad {E S R A} _ _ _ _.

Definition pure {E S R A} (x : A) : esc_monad E S R A :=
  ESCMonad (fun s _ k => k x s).

Definition map {E S R A B} (f : A -> B) (m : esc_monad E S R A) : esc_monad E S R B :=
  ESCMonad (fun s h k => run_esc_monad m s h (fun x => k (f x))).

Definition mapl {E S R A B} (x : B) (m : esc_monad E S R A) : esc_monad E S R B :=
  ESCMonad (fun s h k => run_esc_monad m s h (fun _ => k x)).

Definition app {E S R A B} (m1 : esc_monad E S R (A -> B)) (m2 : esc_monad E S R A) : esc_monad E S R B :=
  ESCMonad (fun s h k => run_esc_monad m1 s h (fun f s => run_esc_monad m2 s h (fun x => k (f x)))).

Definition appl {E S R A B} (m1 : esc_monad E S R A) (m2 : esc_monad E S R B) : esc_monad E S R A :=
  ESCMonad (fun s h k => run_esc_monad m1 s h (fun x s => run_esc_monad m2 s h (fun _ => k x))).

Definition appr {E S R A B} (m1 : esc_monad E S R A) (m2 : esc_monad E S R B) : esc_monad E S R B :=
  ESCMonad (fun s h k => run_esc_monad m1 s h (fun _ s => run_esc_monad m2 s h k)).

Definition bind {E S R A B} (m : esc_monad E S R A) (f : A -> esc_monad E S R B) : esc_monad E S R B :=
  ESCMonad (fun s h k => run_esc_monad m s h (fun x s => run_esc_monad (f x) s h k)).

Definition join {E S R A} (m : esc_monad E S R (esc_monad E S R A)) : esc_monad E S R A :=
  ESCMonad (fun s h k => run_esc_monad m s h (fun m s => run_esc_monad m s h k)).

Definition throw {E S R A} (e : E) : esc_monad E S R A :=
  ESCMonad (fun s h _ => h e s).

Definition except {E S R A} (m : E + A) : esc_monad E S R A :=
  ESCMonad
    (fun s h k =>
       match m with
       | inl e => h e s
       | inr x => k x s
       end).

Definition catch {E S R A} (m : esc_monad E S R A) (f : E -> esc_monad E S R A) : esc_monad E S R A :=
  ESCMonad (fun s h k => run_esc_monad m s (fun e s => run_esc_monad (f e) s h k) k).

Definition try {E S R A} (m : esc_monad E S R A) : esc_monad E S R (E + A) :=
  ESCMonad (fun s _ k => run_esc_monad m s (fun e => k (inl e)) (fun x => k (inr x))).

Definition finally {E S R A} (m1 : esc_monad E S R A) (m2 : esc_monad E S R unit) : esc_monad E S R A :=
  ESCMonad (fun s h k => run_esc_monad m1 s (fun e s => run_esc_monad m2 s h (fun _ => h e)) (fun x s => run_esc_monad m2 s h (fun _ => k x))).

Definition get {E S R} : esc_monad E S R S :=
  ESCMonad (fun s _ k => k s s).

Definition put {E S R} (s : S) : esc_monad E S R unit :=
  ESCMonad (fun _ _ k => k tt s).

Definition state {E S R A} (f : S -> A * S) : esc_monad E S R A :=
  ESCMonad (fun s _ k => let (x, s) := f s in k x s).

Definition gets {E S R A} (f : S -> A) : esc_monad E S R A :=
  ESCMonad (fun s _ k => k (f s) s).

Definition modify {E S R} (f : S -> S) : esc_monad E S R unit :=
  ESCMonad (fun s _ k => k tt (f s)).

Definition cont {E S R A} (f : (A -> R) -> R) : esc_monad E S R A :=
  ESCMonad (fun s _ k => f (fun x => k x s)).

Definition callcc {E S R A B} (f : (A -> esc_monad E S R B) -> esc_monad E S R A) : esc_monad E S R A :=
  ESCMonad (fun s h k => run_esc_monad (f (fun x => ESCMonad (fun _ _ _ => k x s))) s h k).

Definition callcc' {E S R A B} (f : (A -> esc_monad E S R B) -> esc_monad E S R A) : esc_monad E S R A :=
  ESCMonad (fun s h k => run_esc_monad (f (fun x => ESCMonad (fun s _ _ => k x s))) s h k).

Definition map_except {E E' S R A B} (f : E + A -> E' + B) (m : esc_monad E S R A) : esc_monad E' S R B :=
  ESCMonad
    (fun s h k =>
       run_esc_monad m s
         (fun e s =>
            match f (inl e) with
            | inl e => h e s
            | inr x => k x s
            end)
         (fun x s =>
            match f (inr x) with
            | inl e => h e s
            | inr y => k y s
            end)).

Definition with_except {E E' S R A} (f : E -> E') (m : esc_monad E S R A) : esc_monad E' S R A :=
  ESCMonad (fun s h => run_esc_monad m s (fun e => h (f e))).

Definition map_state {E S R A B} (f : A * S -> B * S) (m : esc_monad E S R A) : esc_monad E S R B :=
  ESCMonad (fun s h k => run_esc_monad m s h (fun x s => let (y, s) := f (x, s) in k y s)).

Definition with_state {E S R A} (f : S -> S) (m : esc_monad E S R A) : esc_monad E S R A :=
  ESCMonad (fun s => run_esc_monad m (f s)).

Definition map_cont {E S R A} (f : R -> R) (m : esc_monad E S R A) : esc_monad E S R A :=
  ESCMonad (fun s h k => f (run_esc_monad m s h k)).

Definition with_cont {E S R A B} (f : (B -> R) -> A -> R) (m : esc_monad E S R A) : esc_monad E S R B :=
  ESCMonad (fun s h k => run_esc_monad m s h (fun x s => f (fun y => k y s) x)).

Module ESCMonadNotations.
  Declare Scope esc_monad_scope.
  Delimit Scope esc_monad_scope with esc_monad.
  Bind Scope esc_monad_scope with esc_monad.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : esc_monad_scope.
  Notation "x <$ m" := (mapl x m) (at level 65, right associativity) : esc_monad_scope.
  Notation "m1 <*> m2" := (app m1 m2) (at level 55, left associativity) : esc_monad_scope.
  Notation "m1 <* m2" := (appl m1 m2) (at level 55, left associativity) : esc_monad_scope.
  Notation "m1 *> m2" := (appr m1 m2) (at level 55, left associativity) : esc_monad_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : esc_monad_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : esc_monad_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : esc_monad_scope.
End ESCMonadNotations.
