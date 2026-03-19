From Stdlib Require Import List String ZArith.
From shift_reset.lib Require list.
From shift_reset.lib Require Import int.
From shift_reset.core Require Import syntax ident tuple.
From shift_reset.monad Require except.
From shift_reset.monad Require Import es_monad.
From shift_reset.interpreter Require Import array error iheap imonad unwrap.
Import ESMonadNotations ListNotations.

Local Open Scope Z_scope.
Local Open Scope es_monad_scope.

Definition string_length (v : val) : ivh_monad val :=
  let+ s := iv_monad_to_ivh_monad (unwrap_vstring v) in VInt (Z.of_nat (String.length s)).

Definition array_length (v : val) : ivh_monad val :=
  let+ '(Array _ z) := iv_monad_to_ivh_monad (unwrap_varray v) in VInt z.

Definition tuple_length (v : val) : ivh_monad val :=
  let+ t := iv_monad_to_ivh_monad (unwrap_vtuple v) in VInt (Z.of_nat (tuple_length t)).

Definition array_free (v : val) : ivh_monad val :=
  let* '(Array l z) := iv_monad_to_ivh_monad (unwrap_varray v) in
  let* h := get in
  match array_free_dealloc (Z.to_nat z) l h with
  | Some h' => VTt <$ put h'
  | None => throw (Memory_error "array_free")
  end.

Definition ref_free (v : val) : ivh_monad val :=
  let* l := iv_monad_to_ivh_monad (unwrap_vref v) in
  let* h := get in
  match iheap_dealloc l h with
  | Some h' => VTt <$ put h'
  | None => throw (Memory_error "ref_free")
  end.

Definition int_to_string (v : val) : ivh_monad val :=
  let+ z := iv_monad_to_ivh_monad (unwrap_vint v) in VString (Z_to_string z).

Definition builtin1_registry : list (ident * (val -> ivh_monad val)) :=
  [(Ident "int_to_string", int_to_string);
   (Ident "string_length", string_length);
   (Ident "array_length", array_length);
   (Ident "tuple_length", tuple_length);
   (Ident "ref_free", ref_free);
   (Ident "array_free", array_free)].

Definition dispatch_builtin1 (l : ident) : iv_monad (val -> ivh_monad val) :=
  match list.assoc ident_eqb l builtin1_registry with
  | Some f => except.pure f
  | None => except.throw (Name_error (ident_car l))
  end.

Definition array_make (v1 v2 : val) : ivh_monad val :=
  let* z := iv_monad_to_ivh_monad (unwrap_vint v1) in
  if z <? 0 then throw (Invalid_argument "array_make")
  else state (fun h => (VArray (iheap_next_loc h) z, array_make_alloc (Z.to_nat z) v2 h)).

Definition string_get (v1 v2 : val) : ivh_monad val :=
  let* s := iv_monad_to_ivh_monad (unwrap_vstring v1) in
  let* i := iv_monad_to_ivh_monad (unwrap_vint v2) in
  if i <? 0 then
    throw (Invalid_argument "index out of bounds")
  else
    match String.get (Z.to_nat i) s with
    | Some a => pure (VChar a)
    | None => throw (Invalid_argument "index out of bounds")
    end.

Definition tuple_get (v1 v2 : val) : ivh_monad val :=
  let* t := iv_monad_to_ivh_monad (unwrap_vtuple v1) in
  let* i := iv_monad_to_ivh_monad (unwrap_vint v2) in
  if i <? 0 then
    throw (Invalid_argument "index out of bounds")
  else
    match tuple_get (Z.to_nat i) t with
    | Some v => pure v
    | None => throw (Invalid_argument "index out of bounds")
    end.

Definition builtin2_registry : list (ident * (val -> val -> ivh_monad val)) :=
  [(Ident "array_make", array_make);
   (Ident "string_get", string_get);
   (Ident "tuple_get", tuple_get)].

Definition dispatch_builtin2 (l : ident) : iv_monad (val -> val -> ivh_monad val) :=
  match list.assoc ident_eqb l builtin2_registry with
  | Some f => except.pure f
  | None => except.throw (Name_error (ident_car l))
  end.
