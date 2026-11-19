From Stdlib Require Import List String ZArith.
From shift_reset.lib Require list.
From shift_reset.lib Require Import int.
From shift_reset.core Require Import syntax ident vals.
From shift_reset.monad Require except.
From shift_reset.monad Require Import es_monad.
From shift_reset.interpreter Require Import error iheap imonad unwrap.
Import ESMonadNotations ListNotations.

Local Open Scope Z_scope.
Local Open Scope es_monad_scope.

Definition string_length (v : val) : ivh_monad val :=
  let+ s := iv_monad_to_ivh_monad (unwrap_vstring v) in VInt (Z.of_nat (String.length s)).

Definition array_length (v : val) : ivh_monad val :=
  let+ '(Array _ z) := iv_monad_to_ivh_monad (unwrap_varray v) in VInt z.

Definition tuple_length (v : val) : ivh_monad val :=
  let+ '(Tuple vs) := iv_monad_to_ivh_monad (unwrap_vtuple v) in VInt (Z.of_nat (vals_length vs)).

Definition array_free (v : val) : ivh_monad val :=
  let* '(Array l z) := iv_monad_to_ivh_monad (unwrap_varray v) in
  let* h := get in
  match iheap_dealloc_n (Z.to_nat z) l h with
  | Some h => VTt <$ put h
  | None => throw (Memory_error v)
  end.

Definition ref_free (v : val) : ivh_monad val :=
  let* l := iv_monad_to_ivh_monad (unwrap_vref v) in
  let* h := get in
  match iheap_dealloc l h with
  | Some h => VTt <$ put h
  | None => throw (Memory_error v)
  end.

Definition int_to_string (v : val) : ivh_monad val :=
  let+ z := iv_monad_to_ivh_monad (unwrap_vint v) in VString (Z_to_string z).

Definition array_make (v : val) : ivh_monad val :=
  let* '(v1, v2) := iv_monad_to_ivh_monad (unwrap_vprod v) in
  let* z := iv_monad_to_ivh_monad (unwrap_vint v1) in
  if z <? 0 then throw (Invalid_argument "negative size" v1)
  else let+ l := state (iheap_alloc_n (Z.to_nat z) v2) in VArray l z.

Definition string_get (v : val) : ivh_monad val :=
  let* '(v1, v2) := iv_monad_to_ivh_monad (unwrap_vprod v) in
  let* s := iv_monad_to_ivh_monad (unwrap_vstring v1) in
  let* i := iv_monad_to_ivh_monad (unwrap_vint v2) in
  if i <? 0 then
    throw (Invalid_argument "index out of bounds" v2)
  else
    match String.get (Z.to_nat i) s with
    | Some a => pure (VChar a)
    | None => throw (Invalid_argument "index out of bounds" v2)
    end.

Definition tuple_get (v : val) : ivh_monad val :=
  let* '(v1, v2) := iv_monad_to_ivh_monad (unwrap_vprod v) in
  let* '(Tuple vs) := iv_monad_to_ivh_monad (unwrap_vtuple v1) in
  let* i := iv_monad_to_ivh_monad (unwrap_vint v2) in
  if i <? 0 then
    throw (Invalid_argument "index out of bounds" v2)
  else
    match vals_get (Z.to_nat i) vs with
    | Some v' => pure v'
    | None => throw (Invalid_argument "index out of bounds" v2)
    end.

Definition prim : Type := val -> ivh_monad val.

Definition prim_registry : list (ident * prim) :=
  [(Ident "int_to_string", int_to_string);
   (Ident "string_length", string_length);
   (Ident "array_length", array_length);
   (Ident "tuple_length", tuple_length);
   (Ident "ref_free", ref_free);
   (Ident "array_free", array_free);
   (Ident "array_make", array_make);
   (Ident "string_get", string_get);
   (Ident "tuple_get", tuple_get)].

Definition dispatch_prim (l : ident) : iv_monad prim :=
  match list.assoc ident_eqb l prim_registry with
  | Some f => except.pure f
  | None => except.throw (Name_error (ident_car l))
  end.
