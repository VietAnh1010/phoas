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

Definition throw {R E S A} (e : E) : ces_monad R E S A :=
  CESMonad (fun _ s => (inl e, s)).

Definition except {R E S A} (m : E + A) : ces_monad R E S A :=
  CESMonad
    (fun k s =>
       match m with
       | inl e => (inl e, s)
       | inr x => k x s
       end).

Definition catch {R E S A} (m : ces_monad R E S A) (f : E -> ces_monad R E S A) : ces_monad R E S A :=
  CESMonad
    (fun k s =>
       let (m, s) := run_ces_monad m k s in
       match m with
       | inl e => run_ces_monad (f e) k s
       | inr x => (inr x, s)
       end).

Definition get {R E S} : ces_monad R E S S :=
  CESMonad (fun k s => k s s).

Definition put {R E S} (s : S) : ces_monad R E S unit :=
  CESMonad (fun k _ => k tt s).

Definition state {R E S A} (f : S -> A * S) : ces_monad R E S A :=
  CESMonad (fun k s => let (x, s) := f s in k x s).
