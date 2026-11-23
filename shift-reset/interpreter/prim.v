From Stdlib Require Import List String ZArith.
From shift_reset.lib Require list.
From shift_reset.lib Require Import int.
From shift_reset.core Require Import syntax ident vals.
From shift_reset.monad Require except.
From shift_reset.monad Require Import es_monad.
From shift_reset.interpreter Require Import error iheap imonad unwrap.
Import except.ExceptNotations ESMonadNotations ListNotations.

Local Open Scope Z_scope.
Local Open Scope es_monad_scope.

Definition tuple_length (v : val) : iv_monad val :=
  (let+ '(Tuple vs) := unwrap_tuple v in VInt (Z.of_nat (vals_length vs)))%except.

Definition array_free (v : val) : ivh_monad val :=
  let* '(Array l z) := iv_monad_to_ivh_monad (unwrap_array v) in
  let* h := get in
  match iheap_dealloc_n (Z.to_nat z) l h with
  | None => throw (Memory_error v)
  | Some h => VTt <$ put h
  end.

Definition ref_free (v : val) : ivh_monad val :=
  let* l := iv_monad_to_ivh_monad (unwrap_ref v) in
  let* h := get in
  match iheap_dealloc l h with
  | None => throw (Memory_error v)
  | Some h => VTt <$ put h
  end.

Definition int_to_string (v : val) : iv_monad val :=
  (let+ z := unwrap_int v in VString (Z_to_string z))%except.

Definition array_make (v : val) : ivh_monad val :=
  let* '(v1, v2) := iv_monad_to_ivh_monad (unwrap_prod v) in
  let* z := iv_monad_to_ivh_monad (unwrap_int v1) in
  if z <? 0 then
    throw (Invalid_argument "negative size" v1)
  else
    let+ l := state (iheap_alloc_n (Z.to_nat z) v2) in
    VArray l z.

Definition tuple_get (v : val) : iv_monad val :=
  (let* '(v1, v2) := unwrap_prod v in
   let* '(Tuple vs) := unwrap_tuple v1 in
   let* i := unwrap_int v2 in
   if i <? 0 then
     except.throw (Invalid_argument "index out of bounds" v2)
   else
     match vals_get (Z.to_nat i) vs with
     | None => except.throw (Invalid_argument "index out of bounds" v2)
     | Some v' => except.pure v'
     end)%except.

Definition isolated_applier : Type := val -> val -> ivh_monad val.
Definition prim : Type := isolated_applier -> val -> ivh_monad val.
Definition iv_prim : Type := val -> iv_monad val.
Definition ivh_prim : Type := val -> ivh_monad val.

Definition iv_prim_to_prim (f : iv_prim) (_ : isolated_applier) (v : val) : ivh_monad val :=
  iv_monad_to_ivh_monad (f v).

Definition ivh_prim_to_prim (f : ivh_prim) (_ : isolated_applier) : val -> ivh_monad val :=
  f.

Definition prim_registry : list (ident * prim) :=
  [(Ident "int_to_string", iv_prim_to_prim int_to_string);
   (Ident "tuple_length", iv_prim_to_prim tuple_length);
   (Ident "ref_free", ivh_prim_to_prim ref_free);
   (Ident "array_free", ivh_prim_to_prim array_free);
   (Ident "array_make", ivh_prim_to_prim array_make);
   (Ident "tuple_get", iv_prim_to_prim tuple_get)].

Definition dispatch_prim_aux (apply : isolated_applier) (l : ident) (v : val) : ivh_monad val :=
  match list.assoc ident_eqb l prim_registry with
  | None => throw (Name_error (ident_car l))
  | Some f => f apply v
  end.
