From shift_reset.lib Require Import sum.
From shift_reset.core Require Import syntax.
From shift_reset.interpreter Require Import istate ierror.

Definition imonad (A : Type) : Type := venv -> istate -> (ierror + A) * istate.

Definition imonad_ask_env : imonad venv :=
  fun ve s => (inr ve, s).

Definition imonad_local_env {A} (f : venv -> venv) (m : imonad A) : imonad A :=
  fun ve s => m (f ve) s.

Definition imonad_get_state : imonad istate :=
  fun _ s => (inr s, s).

Definition imonad_set_state (s : istate) : imonad unit :=
  fun _ _ => (inr tt, s).

Definition imonad_modify_state (f : istate -> istate) : imonad unit :=
  fun _ s => (inr tt, f s).

Definition imonad_throw {A} (e : ierror) : imonad A :=
  fun _ s => (inl e, s).

Definition imonad_map {A B} (f : A -> B) (m : imonad A) :=
  fun ve s =>
    let (r, s) := m ve s in
    match r with
    | inl e => (inl e, s)
    | inr x => (inr (f x), s)
    end.

Definition imonad_pure {A} (x : A) : imonad A :=
  fun _ s => (inr x, s).

Definition imonad_lift2 {A B C} (f : A -> B -> C) (m1 : imonad A) (m2 : imonad B) : imonad C :=
  fun ve s =>
    let (r, s) := m1 ve s in
    match r with
    | inl e => (inl e, s)
    | inr x =>
        let (r, s) := m2 ve s in
        match r with
        | inl e => (inl e, s)
        | inr y => (inr (f x y), s)
        end
    end.

Definition imonad_bind {A B} (m : imonad A) (f : A -> imonad B) : imonad B :=
  fun ve s =>
    let (r, s) := m ve s in
    match r with
    | inl e => (inl e, s)
    | inr x => f x ve s
    end.

Definition imonad_then {A B} (m1 : imonad A) (m2 : imonad B) : imonad B :=
  fun ve s =>
    let (r, s) := m1 ve s in
    match r with
    | inl e => (inl e, s)
    | inr _ => m2 ve s
    end.
