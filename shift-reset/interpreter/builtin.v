From Stdlib Require Import List String ZArith.
From shift_reset.lib Require list.
From shift_reset.lib Require Import int.
From shift_reset.core Require Import syntax tag.
From shift_reset.monad Require except.
From shift_reset.monad Require Import es_monad.
From shift_reset.interpreter Require Import array ierror iheap unwrap.

Import ListNotations.
Import ESMonadNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope es_monad_scope.

Definition transform {E S A} (m : except.t E A) : es_monad E S A :=
  ESMonad (fun s => (except.run_except m, s)).

Definition string_length (v : val) : es_monad exn iheap val :=
  let+ s := transform (unwrap_vstring v) in VInt (Z.of_nat (String.length s)).

Definition array_length (v : val) : es_monad exn iheap val :=
  let+ '(Array _ z) := transform (unwrap_varray v) in VInt z.

Definition array_free (v : val) : es_monad exn iheap val :=
  let* '(Array l z) := transform (unwrap_varray v) in
  let* h := get in
  match array_free_dealloc (Z.to_nat z) l h with
  | Some h' => VTt <$ put h'
  | None => throw (Memory_error "array_free")
  end.

Definition ref_free (v : val) : es_monad exn iheap val :=
  let* l := transform (unwrap_vref v) in
  let* h := get in
  match iheap_dealloc l h with
  | Some h' => VTt <$ put h'
  | None => throw (Memory_error "ref_free")
  end.

Definition int_to_string (v : val) : es_monad exn iheap val :=
  let+ z := transform (unwrap_vint v) in VString (Z_to_string z).

Definition builtin1_registry : list (tag * (val -> es_monad exn iheap val)) :=
  [(Tag "int_to_string", int_to_string);
   (Tag "string_length", string_length);
   (Tag "array_length", array_length);
   (Tag "ref_free", ref_free);
   (Tag "array_free", array_free)].

Definition dispatch_builtin1 (tag : tag) : except.t exn (val -> es_monad exn iheap val) :=
  match list.lookup tag_eqb tag builtin1_registry with
  | Some f => except.pure f
  | None => except.throw (Name_error (tag_car tag))
  end.

Definition array_make (v1 v2 : val) : es_monad exn iheap val :=
  let* z := transform (unwrap_vint v1) in
  if (z <? 0)%Z then throw (Invalid_argument "array_make")
  else state (fun h => (VArray (iheap_next_loc h) z, array_make_alloc (Z.to_nat z) v2 h)).

Definition builtin2_registry : list (tag * (val -> val -> es_monad exn iheap val)) :=
  [(Tag "array_make", array_make)].

Definition dispatch_builtin2 (tag : tag) : except.t exn (val -> val -> es_monad exn iheap val) :=
  match list.lookup tag_eqb tag builtin2_registry with
  | Some f => except.pure f
  | None => except.throw (Name_error (tag_car tag))
  end.
