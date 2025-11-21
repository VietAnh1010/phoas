From Stdlib Require Import List String ZArith.
From shift_reset.lib Require list.
From shift_reset.core Require Import syntax tag.
From shift_reset.interpreter Require Import ierror imonad unwrap.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope imonad_scope.

Definition builtin_string_length (v : val) : imonad val :=
  s <- unwrap_vstring v;
  imonad_pure (VInt (Z.of_nat (String.length s))).

Definition builtin_registry : list (tag * (val -> imonad val)) :=
  [(Tag "string_length", builtin_string_length)].

Definition dispatch_builtin (tag : tag) : imonad (val -> imonad val) :=
  match list.lookup tag_eqb tag builtin_registry with
  | Some f => imonad_pure f
  | None => imonad_throw_error (Name_error (tag_car tag))
  end.
