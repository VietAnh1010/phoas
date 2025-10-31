From Stdlib Require Import List.
From shift_reset.core Require Import syntax.
From shift_reset.interpreter Require Import ierror iheap.
Import ListNotations.

Record imonad (A : Type) : Type := IMonad { imonad_run : env -> iheap -> (ierror + A) * iheap }.

Arguments IMonad {A} _.
Arguments imonad_run {A} _ _ _.

Definition imonad_ask_env : imonad env :=
  IMonad (fun env h => (inr env, h)).

Definition imonad_asks_env {A} (f : env -> A) : imonad A :=
  IMonad (fun env h => (inr (f env), h)).

Definition imonad_local_env {A} (f : env -> env) (m : imonad A) : imonad A :=
  IMonad (fun env => imonad_run m (f env)).

Definition imonad_under_env {A} (env : env) (m : imonad A) : imonad A :=
  IMonad (fun _ => imonad_run m env).

Definition imonad_get_heap : imonad iheap :=
  IMonad (fun _ h => (inr h, h)).

Definition imonad_set_heap (h : iheap) : imonad unit :=
  IMonad (fun _ _ => (inr tt, h)).

Definition imonad_state_heap {A} (f : iheap -> A * iheap) : imonad A :=
  IMonad (fun _ h => let (x, h) := f h in (inr x, h)).

Definition imonad_gets_heap {A} (f : iheap -> A) : imonad A :=
  IMonad (fun _ h => (inr (f h), h)).

Definition imonad_modify_heap (f : iheap -> iheap) : imonad unit :=
  IMonad (fun _ h => (inr tt, f h)).

Definition imonad_map_heap {A B} (f : A * iheap -> B * iheap) (m : imonad A) : imonad B :=
  IMonad (fun env h =>
            let (r, h) := imonad_run m env h in
            match r with
            | inl e => (inl e, h)
            | inr x => let (y, h) := f (x, h) in (inr y, h)
            end).

Definition imonad_with_heap {A} (f : iheap -> iheap) (m : imonad A) : imonad A :=
  IMonad (fun env h => imonad_run m env (f h)).

Definition imonad_throw_error {A} (e : ierror) : imonad A :=
  IMonad (fun _ h => (inl e, h)).

Definition imonad_catch_error {A} (m : imonad A) (f : ierror -> imonad A) : imonad A :=
  IMonad (fun env h =>
            let p := imonad_run m env h in
            let (r, h) := p in
            match r with
            | inl e => imonad_run (f e) env h
            | inr _ => p
            end).

Definition imonad_handle_error {A} (f : ierror -> imonad A) (m : imonad A) : imonad A :=
  imonad_catch_error m f.

Definition imonad_try_error {A} (m : imonad A) : imonad (ierror + A) :=
  IMonad (fun env h => let (r, h) := imonad_run m env h in (inr r, h)).

Definition imonad_except_error {A} (r : ierror + A) : imonad A :=
  IMonad (fun _ h => (r, h)).

Definition imonad_with_error {A} (f : ierror -> ierror) (m : imonad A) : imonad A :=
  IMonad (fun env h =>
            let p := imonad_run m env h in
            let (r, h) := p in
            match r with
            | inl e => (inl (f e), h)
            | inr _ => p
            end).

Definition imonad_map_error {A B} (f : ierror + A -> ierror + B) (m : imonad A) : imonad B :=
  IMonad (fun env h => let (r, h) := imonad_run m env h in (f r, h)).

Definition imonad_map {A B} (f : A -> B) (m : imonad A) :=
  IMonad (fun env h =>
            let (r, h) := imonad_run m env h in
            match r with
            | inl e => (inl e, h)
            | inr x => (inr (f x), h)
            end).

Definition imonad_replace {A B} (x : A) (m : imonad B) : imonad A :=
  IMonad (fun env h =>
            let (r, h) := imonad_run m env h in
            match r with
            | inl e => (inl e, h)
            | inr _ => (inr x, h)
            end).

Definition imonad_pure {A} (x : A) : imonad A :=
  IMonad (fun _ h => (inr x, h)).

Definition imonad_app {A B} (m1 : imonad (A -> B)) (m2 : imonad A) : imonad B :=
  IMonad (fun env h =>
            let (r, h) := imonad_run m1 env h in
            match r with
            | inl e => (inl e, h)
            | inr f => let (r, h) := imonad_run m2 env h in
                       match r with
                       | inl e => (inl e, h)
                       | inr x => (inr (f x), h)
                       end
            end).

Definition imonad_lift2 {A B C} (f : A -> B -> C) (m1 : imonad A) (m2 : imonad B) : imonad C :=
  IMonad (fun env h =>
            let (r, h) := imonad_run m1 env h in
            match r with
            | inl e => (inl e, h)
            | inr x => let (r, h) := imonad_run m2 env h in
                       match r with
                       | inl e => (inl e, h)
                       | inr y => (inr (f x y), h)
                       end
            end).

Definition imonad_bind {A B} (m : imonad A) (f : A -> imonad B) : imonad B :=
  IMonad (fun env h =>
            let (r, h) := imonad_run m env h in
            match r with
            | inl e => (inl e, h)
            | inr x => imonad_run (f x) env h
            end).

Definition imonad_then {A B} (m1 : imonad A) (m2 : imonad B) : imonad B :=
  IMonad (fun env h =>
            let (r, h) := imonad_run m1 env h in
            match r with
            | inl e => (inl e, h)
            | inr _ => imonad_run m2 env h
            end).

Definition imonad_join {A} (m : imonad (imonad A)) : imonad A :=
  IMonad (fun env h =>
            let (r, h) := imonad_run m env h in
            match r with
            | inl e => (inl e, h)
            | inr m => imonad_run m env h
            end).

Definition imonad_eval {A} (m : imonad A) (env : env) (h : iheap) : ierror + A :=
  fst (imonad_run m env h).

Definition imonad_exec {A} (m : imonad A) (env : env) (h : iheap) : iheap :=
  snd (imonad_run m env h).

Declare Scope imonad_scope.
Delimit Scope imonad_scope with imonad.
Bind Scope imonad_scope with imonad.
Local Open Scope imonad_scope.

Notation "f <$> m" := (imonad_map f m) (at level 65, right associativity) : imonad_scope.
Notation "x <$ m" := (imonad_replace x m) (at level 65, right associativity) : imonad_scope.
Notation "m1 <*> m2" := (imonad_app m1 m2) (at level 55, left associativity) : imonad_scope.
Notation "m >>= f" := (imonad_bind m f) (at level 50, left associativity) : imonad_scope.
Notation "m1 >> m2" := (imonad_then m1 m2) (at level 50, left associativity) : imonad_scope.

Notation "x <- m1 ; m2" := (imonad_bind m1 (fun x => m2)) (at level 100, right associativity) : imonad_scope.
Notation "m1 ;; m2" := (imonad_bind m1 (fun _ => m2)) (at level 100, right associativity) : imonad_scope.

Definition imonad_kleisli_compose {A B C} (f1 : A -> imonad B) (f2 : B -> imonad C) (x : A) : imonad C :=
  f1 x >>= f2.

Fixpoint imonad_list_map {A B} (f : A -> imonad B) (xs : list A) : imonad (list B) :=
  match xs with
  | [] => imonad_pure []
  | x :: xs' => y <- f x; cons y <$> imonad_list_map f xs'
  end.

Fixpoint imonad_list_forall2b {A B} (f : A -> B -> imonad bool) (xs : list A) (ys : list B) : imonad bool :=
  match xs, ys with
  | [], [] => imonad_pure true
  | x :: xs', y :: ys' => b <- f x y; if b then imonad_list_forall2b f xs' ys' else imonad_pure false
  | _, _ => imonad_pure false
  end.

Notation "f1 >=> f2" := (imonad_kleisli_compose f1 f2) (at level 60, right associativity) : imonad_scope.
