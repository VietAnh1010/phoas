From Stdlib Require Import ZArith String.
From shift_reset Require Import loc var.

Inductive prim1 : Type :=
| prim1_neg : prim1
| prim1_ref : prim1
| prim1_get : prim1
| prim1_free : prim1
| prim1_fst : prim1
| prim1_snd : prim1.

Definition prim1_eq_dec : forall (op1 op2 : prim1), {op1 = op2} + {op1 <> op2}.
Proof. decide equality. Defined.

Inductive prim2 : Type :=
| prim2_add : prim2
| prim2_sub : prim2
| prim2_mul : prim2
| prim2_eq : prim2
| prim2_lt : prim2
| prim2_set : prim2
| prim2_cat : prim2 (* string *)
| prim2_pair : prim2.

Definition prim2_eq_dec : forall (op1 op2 : prim2), {op1 = op2} + {op1 <> op2}.
Proof. decide equality. Defined.

Inductive val : Type :=
| val_unit : val
| val_bool : bool -> val
| val_int : Z -> val
| val_loc : loc -> val
| val_fun : var -> expr -> val
| val_fix : var -> var -> expr -> val
| val_str : string -> val
| val_pair : val -> val -> val
with atom : Type :=
| atom_val : val -> atom
| atom_var : var -> atom
with expr : Type :=
| expr_atom : atom -> expr
| expr_app : atom -> atom -> expr
| expr_let : var -> expr -> expr -> expr
| expr_if : atom -> expr -> expr -> expr
| expr_prim1 : prim1 -> atom -> expr
| expr_prim2 : prim2 -> atom -> atom -> expr
| expr_shift : var -> expr -> expr
| expr_reset : expr -> expr
| expr_cont : expr -> var -> expr -> expr.
