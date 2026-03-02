Record imonad (R S E A : Type) : Type := IMonad { imonad_run : R -> S -> (E + A) * S }.

Arguments IMonad {R S E A} _.
Arguments imonad_run {R S E A} _ _ _.

Definition imonad_ask {R S E} : imonad R S E R :=
  IMonad (fun r s => (inr r, s)).

Definition imonad_asks {R S E A} (f : R -> A) : imonad R S E A :=
  IMonad (fun r s => (inr (f r), s)).

Definition imonad_local {R S E A} (f : R -> R) (m : imonad R S E A) : imonad R S E A :=
  IMonad (fun r => imonad_run m (f r)).

Definition imonad_under {R S E A} (r : R) (m : imonad R S E A) : imonad R S E A :=
  IMonad (fun _ => imonad_run m r).

Definition imonad_with_reader {R R' S E A} (f : R' -> R) (m : imonad R S E A) : imonad R' S E A :=
  IMonad (fun r' => imonad_run m (f r')).

Definition imonad_get {R S E} : imonad R S E S :=
  IMonad (fun _ s => (inr s, s)).

Definition imonad_put {R S E} (s : S) : imonad R S E unit :=
  IMonad (fun _ _ => (inr tt, s)).

Definition imonad_state {R S E A} (f : S -> A * S) : imonad R S E A :=
  IMonad (fun _ s => let (x, s) := f s in (inr x, s)).

Definition imonad_gets {R S E A} (f : S -> A) : imonad R S E A :=
  IMonad (fun _ s => (inr (f s), s)).

Definition imonad_modify {R S E} (f : S -> S) : imonad R S E unit :=
  IMonad (fun _ s => (inr tt, f s)).

Definition imonad_map_state {R S E A B} (f : A * S -> B * S) (m : imonad R S E A) : imonad R S E B :=
  IMonad (fun r s =>
            let (m, s) := imonad_run m r s in
            match m with
            | inl e => (inl e, s)
            | inr x => let (y, s) := f (x, s) in (inr y, s)
            end).

Definition imonad_with_state {R S E A} (f : S -> S) (m : imonad R S E A) : imonad R S E A :=
  IMonad (fun r s => imonad_run m r (f s)).

Definition imonad_throw {R S E A} (e : E) : imonad R S E A :=
  IMonad (fun _ s => (inl e, s)).

Definition imonad_catch {R S E E' A} (m : imonad R S E A) (f : E -> imonad R S E' A) : imonad R S E' A :=
  IMonad (fun r s =>
            let (m, s) := imonad_run m r s in
            match m with
            | inl e => imonad_run (f e) r s
            | inr x => (inr x, s)
            end).

Definition imonad_handle {R S E E' A} (f : E -> imonad R S E' A) (m : imonad R S E A) : imonad R S E' A :=
  IMonad (fun r s =>
            let (m, s) := imonad_run m r s in
            match m with
            | inl e => imonad_run (f e) r s
            | inr x => (inr x, s)
            end).

Definition imonad_try {R S E A} (m : imonad R S E A) : imonad R S E (E + A) :=
  IMonad (fun r s => let (m, s) := imonad_run m r s in (inr m, s)).

Definition imonad_finally {R S E A} (m1 : imonad R S E A) (m2 : imonad R S E unit) : imonad R S E A :=
  IMonad (fun r s =>
            let (m1, s) := imonad_run m1 r s in
            let (m2, s) := imonad_run m2 r s in
            match m2 with
            | inl e => (inl e, s)
            | inr _ => (m1, s)
            end).

Definition imonad_except {R S E A} (m : E + A) : imonad R S E A :=
  IMonad (fun _ s => (m, s)).

Definition imonad_with_except {R S E E' A} (f : E -> E') (m : imonad R S E A) : imonad R S E' A :=
  IMonad (fun r s =>
            let (m, s) := imonad_run m r s in
            match m with
            | inl e => (inl (f e), s)
            | inr x => (inr x, s)
            end).

Definition imonad_map_except {R S E E' A B} (f : E + A -> E' + B) (m : imonad R S E A) : imonad R S E' B :=
  IMonad (fun r s => let (m, s) := imonad_run m r s in (f m, s)).

Definition imonad_map {R S E A B} (f : A -> B) (m : imonad R S E A) : imonad R S E B :=
  IMonad (fun r s =>
            let (m, s) := imonad_run m r s in
            match m with
            | inl e => (inl e, s)
            | inr x => (inr (f x), s)
            end).

Definition imonad_replace {R S E A B} (x : B) (m : imonad R S E A) : imonad R S E B :=
  IMonad (fun r s =>
            let (m, s) := imonad_run m r s in
            match m with
            | inl e => (inl e, s)
            | inr _ => (inr x, s)
            end).

Definition imonad_pure {R S E A} (x : A) : imonad R S E A :=
  IMonad (fun _ s => (inr x, s)).

Definition imonad_app {R S E A B} (m1 : imonad R S E (A -> B)) (m2 : imonad R S E A) : imonad R S E B :=
  IMonad (fun r s =>
            let (m, s) := imonad_run m1 r s in
            match m with
            | inl e => (inl e, s)
            | inr f =>
                let (m, s) := imonad_run m2 r s in
                match m with
                | inl e => (inl e, s)
                | inr x => (inr (f x), s)
                end
            end).

Definition imonad_lift2 {R S E A B C} (f : A -> B -> C) (m1 : imonad R S E A) (m2 : imonad R S E B) : imonad R S E C :=
  IMonad (fun r s =>
            let (m, s) := imonad_run m1 r s in
            match m with
            | inl e => (inl e, s)
            | inr x =>
                let (m, s) := imonad_run m2 r s in
                match m with
                | inl e => (inl e, s)
                | inr y => (inr (f x y), s)
                end
            end).

Definition imonad_bind {R S E A B} (m : imonad R S E A) (f : A -> imonad R S E B) : imonad R S E B :=
  IMonad (fun r s =>
            let (m, s) := imonad_run m r s in
            match m with
            | inl e => (inl e, s)
            | inr x => imonad_run (f x) r s
            end).

Definition imonad_then {R S E A B} (m1 : imonad R S E A) (m2 : imonad R S E B) : imonad R S E B :=
  IMonad (fun r s =>
            let (m, s) := imonad_run m1 r s in
            match m with
            | inl e => (inl e, s)
            | inr _ => imonad_run m2 r s
            end).

Definition imonad_join {R S E A} (m : imonad R S E (imonad R S E A)) : imonad R S E A :=
  IMonad (fun r s =>
            let (m, h) := imonad_run m r s in
            match m with
            | inl e => (inl e, h)
            | inr m => imonad_run m r h
            end).

Definition imonad_kleisli_compose {R S E A B C} (f1 : A -> imonad R S E B) (f2 : B -> imonad R S E C) (x : A) : imonad R S E C :=
  imonad_bind (f1 x) f2.

Definition imonad_eval {R S E A} (m : imonad R S E A) (r : R) (s : S) : E + A :=
  fst (imonad_run m r s).

Definition imonad_exec {R S E A} (m : imonad R S E A) (r : R) (s : S) : S :=
  snd (imonad_run m r s).

Declare Scope imonad_scope.
Delimit Scope imonad_scope with imonad.
Bind Scope imonad_scope with imonad.
Local Open Scope imonad_scope.

Notation "f <$> m" := (imonad_map f m) (at level 65, right associativity) : imonad_scope.
Notation "x <$ m" := (imonad_replace x m) (at level 65, right associativity) : imonad_scope.
Notation "m1 <*> m2" := (imonad_app m1 m2) (at level 55, left associativity) : imonad_scope.
Notation "m >>= f" := (imonad_bind m f) (at level 50, left associativity) : imonad_scope.
Notation "m1 >> m2" := (imonad_then m1 m2) (at level 50, left associativity) : imonad_scope.
Notation "f1 >=> f2" := (imonad_kleisli_compose f1 f2) (at level 60, right associativity) : imonad_scope.

Notation "let+ x := m 'in' y" :=
  (imonad_map (fun x => y) m) (at level 100, x binder, right associativity) : imonad_scope.

Notation "let* x := m1 'in' m2" :=
  (imonad_bind m1 (fun x => m2)) (at level 100, x binder, right associativity) : imonad_scope.
