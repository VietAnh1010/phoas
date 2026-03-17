Record res_monad (R E S A : Type) : Type := RESMonad { run_res_monad : R -> S -> (E + A) * S }.
Definition t : Type -> Type -> Type -> Type -> Type := res_monad.

Arguments RESMonad {R E S A} _.
Arguments run_res_monad {R E S A} _ _ _.

Definition pure {R E S A} (x : A) : res_monad R E S A :=
  RESMonad (fun _ s => (inr x, s)).

Definition map {R E S A B} (f : A -> B) (m : res_monad R E S A) : res_monad R E S B :=
  RESMonad
    (fun r s =>
       let (m, s) := run_res_monad m r s in
       match m with
       | inl e => (inl e, s)
       | inr x => (inr (f x), s)
       end).

Definition mapl {R E S A B} (x : B) (m : res_monad R E S A) : res_monad R E S B :=
  RESMonad
    (fun r s =>
       let (m, s) := run_res_monad m r s in
       match m with
       | inl e => (inl e, s)
       | inr _ => (inr x, s)
       end).

Definition app {R E S A B} (m1 : res_monad R E S (A -> B)) (m2 : res_monad R E S A) : res_monad R E S B :=
  RESMonad
    (fun r s =>
       let (m, s) := run_res_monad m1 r s in
       match m with
       | inl e => (inl e, s)
       | inr f =>
           let (m, s) := run_res_monad m2 r s in
           match m with
           | inl e => (inl e, s)
           | inr x => (inr (f x), s)
           end
       end).

Definition appl {R E S A B} (m1 : res_monad R E S A) (m2 : res_monad R E S B) : res_monad R E S A :=
  RESMonad
    (fun r s =>
       let (m, s) := run_res_monad m1 r s in
       match m with
       | inl e => (inl e, s)
       | inr x =>
           let (m, s) := run_res_monad m2 r s in
           match m with
           | inl e => (inl e, s)
           | inr _ => (inr x, s)
           end
       end).

Definition appr {R E S A B} (m1 : res_monad R E S A) (m2 : res_monad R E S B) : res_monad R E S B :=
  RESMonad
    (fun r s =>
       let (m, s) := run_res_monad m1 r s in
       match m with
       | inl e => (inl e, s)
       | inr x => run_res_monad m2 r s
       end).

Definition bind {R E S A B} (m : res_monad R E S A) (f : A -> res_monad R E S B) : res_monad R E S B :=
  RESMonad
    (fun r s =>
       let (m, s) := run_res_monad m r s in
       match m with
       | inl e => (inl e, s)
       | inr x => run_res_monad (f x) r s
       end).

Definition join {R E S A} (m : res_monad R E S (res_monad R E S A)) : res_monad R E S A :=
  RESMonad
    (fun r s =>
       let (m, s) := run_res_monad m r s in
       match m with
       | inl e => (inl e, s)
       | inr m => run_res_monad m r s
       end).

Definition ask {R E S} : res_monad R E S R :=
  RESMonad (fun r s => (inr r, s)).

Definition reader {R E S A} (f : R -> A) : res_monad R E S A :=
  RESMonad (fun r s => (inr (f r), s)).

Definition local {R E S A} (f : R -> R) (m : res_monad R E S A) : res_monad R E S A :=
  RESMonad (fun r => run_res_monad m (f r)).

Definition scope {R E S A} (r : R) (m : res_monad R E S A) : res_monad R E S A :=
  RESMonad (fun _ => run_res_monad m r).

Definition get {R E S} : res_monad R E S S :=
  RESMonad (fun _ s => (inr s, s)).

Definition put {R E S} (s : S) : res_monad R E S unit :=
  RESMonad (fun _ _ => (inr tt, s)).

Definition state {R E S A} (f : S -> A * S) : res_monad R E S A :=
  RESMonad (fun _ s => let (x, s) := f s in (inr x, s)).

Definition gets {R E S A} (f : S -> A) : res_monad R E S A :=
  RESMonad (fun _ s => (inr (f s), s)).

Definition modify {R E S} (f : S -> S) : res_monad R E S unit :=
  RESMonad (fun _ s => (inr tt, f s)).

Definition throw {R E S A} (e : E) : res_monad R E S A :=
  RESMonad (fun _ s => (inl e, s)).

Definition except {R E S A} (m : E + A) : res_monad R E S A :=
  RESMonad (fun _ s => (m, s)).

Definition catch {R E S A} (m : res_monad R E S A) (f : E -> res_monad R E S A) : res_monad R E S A :=
  RESMonad
    (fun r s =>
       let (m, s) := run_res_monad m r s in
       match m with
       | inl e => run_res_monad (f e) r s
       | inr x => (inr x, s)
       end).

Definition try {R E S A} (m : res_monad R E S A) : res_monad R E S (E + A) :=
  RESMonad (fun r s => let (m, s) := run_res_monad m r s in (inr m, s)).

Definition finally {R E S A} (m1 : res_monad R E S A) (m2 : res_monad R E S unit) : res_monad R E S A :=
  RESMonad
    (fun r s =>
       let (m1, s) := run_res_monad m1 r s in
       let (m2, s) := run_res_monad m2 r s in
       match m2 with
       | inl e => (inl e, s)
       | inr _ => (m1, s)
       end).

Definition with_reader {R' R E S A} (f : R' -> R) (m : res_monad R E S A) : res_monad R' E S A :=
  RESMonad (fun r => run_res_monad m (f r)).

Definition map_state {R E S A B} (f : A * S -> B * S) (m : res_monad R E S A) : res_monad R E S B :=
  RESMonad
    (fun r s =>
       let (m, s) := run_res_monad m r s in
       match m with
       | inl e => (inl e, s)
       | inr x => let (y, s) := f (x, s) in (inr y, s)
       end).

Definition with_state {R E S A} (f : S -> S) (m : res_monad R E S A) : res_monad R E S A :=
  RESMonad (fun r s => run_res_monad m r (f s)).

Definition map_except {R E E' S A B} (f : E + A -> E' + B) (m : res_monad R E S A) : res_monad R E' S B :=
  RESMonad (fun r s => let (m, s) := run_res_monad m r s in (f m, s)).

Definition with_except {R E E' S A} (f : E -> E') (m : res_monad R E S A) : res_monad R E' S A :=
  RESMonad
    (fun r s =>
       let (m, s) := run_res_monad m r s in
       match m with
       | inl e => (inl (f e), s)
       | inr x => (inr x, s)
       end).

Definition map_res_monad {R E E' S A B} (f : (E + A) * S -> (E' + B) * S) (m : res_monad R E S A) : res_monad R E' S B :=
  RESMonad (fun r s => f (run_res_monad m r s)).

Definition with_res_monad {R' R E S A} (f : R' -> S -> R * S) (m : res_monad R E S A) : res_monad R' E S A :=
  RESMonad (fun r s => let (r, s) := f r s in run_res_monad m r s).

Module RESMonadNotations.
  Declare Scope res_monad_scope.
  Delimit Scope res_monad_scope with res_monad.
  Bind Scope res_monad_scope with res_monad.

  Notation "f <$> m" := (map f m) (at level 65, right associativity) : res_monad_scope.
  Notation "x <$ m" := (mapl x m) (at level 65, right associativity) : res_monad_scope.
  Notation "m1 <*> m2" := (app m1 m2) (at level 55, left associativity) : res_monad_scope.
  Notation "m1 <* m2" := (appl m1 m2) (at level 55, left associativity) : res_monad_scope.
  Notation "m1 *> m2" := (appr m1 m2) (at level 55, left associativity) : res_monad_scope.
  Notation "m >>= f" := (bind m f) (at level 50, left associativity) : res_monad_scope.

  Notation "let+ x := m 'in' k" := (map (fun x => k) m) (at level 100, x binder, right associativity) : res_monad_scope.
  Notation "let* x := m 'in' k" := (bind m (fun x => k)) (at level 100, x binder, right associativity) : res_monad_scope.
End RESMonadNotations.
