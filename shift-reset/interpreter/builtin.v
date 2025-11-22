From Stdlib Require Import List String ZArith.
From shift_reset.lib Require list.
From shift_reset.lib Require Import int.
From shift_reset.core Require Import syntax loc tag.
From shift_reset.interpreter Require Import array ierror iheap imonad unwrap.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope imonad_scope.

Definition string_length (v : val) : imonad val :=
  let+ s := unwrap_vstring v in VInt (Z.of_nat (String.length s)).

Definition array_length (v : val) : imonad val :=
  let+ '(Array _ z) := unwrap_varray v in VInt z.

Definition array_free (v : val) : imonad val :=
  let* '(Array l z) := unwrap_varray v in
  let* h := imonad_get_heap in
  match array_free_dealloc (Z.to_nat z) l h with
  | Some h' => VTt <$ imonad_set_heap h'
  | None => imonad_throw_error (Memory_error "array_free")
  end.

Definition ref_free (v : val) : imonad val :=
  let* l := unwrap_vref v in
  let* h := imonad_get_heap in
  match iheap_dealloc l h with
  | Some h' => VTt <$ imonad_set_heap h'
  | None => imonad_throw_error (Memory_error "ref_free")
  end.

Definition int_to_string (v : val) : imonad val :=
  let+ z := unwrap_vint v in VString (Z_to_string z).

Definition builtin1_registry : list (tag * (val -> imonad val)) :=
  [(Tag "int_to_string", int_to_string);
   (Tag "string_length", string_length);
   (Tag "array_length", array_length);
   (Tag "ref_free", ref_free);
   (Tag "array_free", array_free)].

Definition dispatch_builtin1 (tag : tag) : imonad (val -> imonad val) :=
  match list.lookup tag_eqb tag builtin1_registry with
  | Some f => imonad_pure f
  | None => imonad_throw_error (Name_error (tag_car tag))
  end.

Definition array_make (v1 v2 : val) : imonad val :=
  let* z := unwrap_vint v1 in
  let* h := imonad_get_heap in
  VArray (iheap_next_loc h) z <$ imonad_set_heap (array_make_alloc (Z.to_nat z) v2 h).

Definition builtin2_registry : list (tag * (val -> val -> imonad val)) :=
  [(Tag "array_make", array_make)].

Definition dispatch_builtin2 (tag : tag) : imonad (val -> val -> imonad val) :=
  match list.lookup tag_eqb tag builtin2_registry with
  | Some f => imonad_pure f
  | None => imonad_throw_error (Name_error (tag_car tag))
  end.
