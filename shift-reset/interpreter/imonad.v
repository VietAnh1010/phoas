From shift_reset.lib Require Import sum.
From shift_reset.core Require Import syntax.
From shift_reset.interpreter Require Import istate ierror.

Definition imonad (A : Type) : Type := env -> istate -> (ierror + A) * istate.

Definition imonad_ask_env : imonad env :=
  fun env s => (inr env, s).

Definition imonad_local_env {A} (f : env -> env) (m : imonad A) : imonad A :=
  fun env s => m (f env) s.

Definition imonad_get_state : imonad istate :=
  fun _ s => (inr s, s).

Definition imonad_set_state (s : istate) : imonad unit :=
  fun _ _ => (inr tt, s).

Definition imonad_modify_state (f : istate -> istate) : imonad unit :=
  fun _ s => (inr tt, f s).

Definition imonad_throw {A} (e : ierror) : imonad A :=
  fun _ s => (inl e, s).

Definition imonad_map {A B} (f : A -> B) (m : imonad A) :=
  fun env s =>
    let (r, s) := m env s in
    match r with
    | inl e => (inl e, s)
    | inr x => (inr (f x), s)
    end.

Definition imonad_pure {A} (x : A) : imonad A :=
  fun _ s => (inr x, s).

Definition imonad_lift2 {A B C} (f : A -> B -> C) (m1 : imonad A) (m2 : imonad B) : imonad C :=
  fun env s =>
    let (r, s) := m1 env s in
    match r with
    | inl e => (inl e, s)
    | inr x =>
        let (r, s) := m2 env s in
        match r with
        | inl e => (inl e, s)
        | inr y => (inr (f x y), s)
        end
    end.

Definition imonad_bind {A B} (m : imonad A) (f : A -> imonad B) : imonad B :=
  fun env s =>
    let (r, s) := m env s in
    match r with
    | inl e => (inl e, s)
    | inr x => f x env s
    end.

Definition imonad_then {A B} (m1 : imonad A) (m2 : imonad B) : imonad B :=
  fun env s =>
    let (r, s) := m1 env s in
    match r with
    | inl e => (inl e, s)
    | inr _ => m2 env s
    end.
