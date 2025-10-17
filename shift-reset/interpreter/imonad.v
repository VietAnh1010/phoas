From shift_reset.lib Require Import sum.
From shift_reset.core Require Import syntax.
From shift_reset.interpreter Require Import ierror iheap.

Record imonad (A : Type) : Type := IMonad { imonad_run : env -> iheap -> (ierror + A) * iheap }.

Arguments IMonad {A} _.
Arguments imonad_run {A} _ _ _.

Definition imonad_ask_env : imonad env :=
  IMonad (fun env h => (inr env, h)).

Definition imonad_local_env {A} (f : env -> env) (m : imonad A) : imonad A :=
  IMonad (fun env => imonad_run m (f env)).

Definition imonad_get_heap : imonad iheap :=
  IMonad (fun _ h => (inr h, h)).

Definition imonad_set_heap (h : iheap) : imonad unit :=
  IMonad (fun _ _ => (inr tt, h)).

Definition imonad_modify_heap (f : iheap -> iheap) : imonad unit :=
  IMonad (fun _ h => (inr tt, f h)).

Definition imonad_throw {A} (e : ierror) : imonad A :=
  IMonad (fun _ h => (inl e, h)).

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

Definition imonad_eval {A} (m : imonad A) (env : env) (h : iheap) : ierror + A :=
  fst (imonad_run m env h).

Definition imonad_exec {A} (m : imonad A) (env : env) (h : iheap) : iheap :=
  snd (imonad_run m env h).

Definition imonad_kleisli_compose {A B C} (f1 : A -> imonad B) (f2 : B -> imonad C) (x : A) : imonad C :=
  imonad_bind (f1 x) f2.

Declare Scope imonad_scope.
Delimit Scope imonad_scope with imonad.
Bind Scope imonad_scope with imonad.

Notation "f <$> m" := (imonad_map f m) (at level 65, left associativity) : imonad_scope.
Notation "x <$ m" := (imonad_replace x m) (at level 65, left associativity) : imonad_scope.
Notation "m >>= f" := (imonad_bind m f) (at level 60, right associativity) : imonad_scope.
Notation "m1 >> m2" := (imonad_then m1 m2) (at level 60, right associativity) : imonad_scope.
Notation "f1 >=> f2" := (imonad_kleisli_compose f1 f2) (at level 60, right associativity) : imonad_scope.

Notation "x <- m1 ; m2" := (imonad_bind m1 (fun x => m2)) (at level 100, right associativity) : imonad_scope.
Notation "m1 ;; m2" := (imonad_then m1 m2) (at level 100, right associativity) : imonad_scope.
