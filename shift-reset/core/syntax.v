From Stdlib Require Import Bool ZArith.
From shift_reset.core Require Import loc var.

Inductive prim1 : Type :=
| P1Neg : prim1
| P1Not : prim1.

Inductive prim2 : Type :=
| P2Add : prim2
| P2Sub : prim2
| P2Mul : prim2
| P2Div : prim2
| P2Rem : prim2
| P2And : prim2
| P2Or : prim2
| P2Xor : prim2
| P2Eq : prim2
| P2Lt : prim2
| P2Le : prim2.

Inductive binder : Type :=
| BAnon : binder
| BVar : var -> binder.

Inductive val : Type :=
| VUnit : val
| VBool : bool -> val
| VInt : Z -> val
| VFun : expr1 -> venv -> val
| VFix : expr2 -> venv -> val
| VPair : val -> val -> val
| VInl : val -> val
| VInr : val -> val
| VLoc : loc -> val
with atom : Type :=
| AVal : val -> atom
| AVar : var -> atom
with expr : Type :=
| EAtom : atom -> expr
| ELet : expr -> expr1 -> expr
| EIf : atom -> expr -> expr -> expr
| EPrim1 : prim1 -> atom -> expr
| EPrim2 : prim2 -> atom -> atom -> expr
| EFun : expr1 -> expr
| EFix : expr2 -> expr
| EApp : atom -> atom -> expr
| EPair : atom -> atom -> expr
| EFst : atom -> expr
| ESnd : atom -> expr
| EInl : atom -> expr
| EInr : atom -> expr
| ECase : atom -> expr1 -> expr1 -> expr
| ERef : atom -> expr
| EGet : atom -> expr
| ESet : atom -> atom -> expr
| EFree : atom -> expr
| EShift : expr1 -> expr
| EReset : expr -> expr
| ECont : expr -> expr1 -> expr
with expr1 : Type :=
| E1 : binder -> expr -> expr1
with expr2 : Type :=
| E2 : binder -> expr1 -> expr2
with venv : Type :=
| VENil : venv
| VECons : var -> val -> venv -> venv.

Definition prim1_eq_dec : forall (p1 p2 : prim1), {p1 = p2} + {p1 <> p2}.
Proof. decide equality. Defined.

Definition prim2_eq_dec : forall (p1 p2 : prim2), {p1 = p2} + {p1 <> p2}.
Proof. decide equality. Defined.

Definition binder_eq_dec : forall (b1 b2 : binder), {b1 = b2} + {b1 <> b2}.
Proof. decide equality; auto using var_eq_dec. Defined.

Fixpoint val_eq_dec : forall (v1 v2 : val), {v1 = v2} + {v1 <> v2}
with atom_eq_dec : forall (a1 a2 : atom), {a1 = a2} + {a1 <> a2}
with expr_eq_dec : forall (e1 e2 : expr), {e1 = e2} + {e1 <> e2}
with expr1_eq_dec : forall (e1 e2 : expr1), {e1 = e2} + {e1 <> e2}
with expr2_eq_dec : forall (e1 e2 : expr2), {e1 = e2} + {e1 <> e2}
with venv_eq_dec : forall (ve1 ve2 : venv), {ve1 = ve2} + {ve1 <> ve2}.
Proof.
  { decide equality; auto using bool_dec, Z.eq_dec, loc_eq_dec. }
  { decide equality; auto using var_eq_dec. }
  { decide equality; auto using prim1_eq_dec, prim2_eq_dec. }
  { decide equality; auto using binder_eq_dec. }
  { decide equality; auto using binder_eq_dec. }
  { decide equality; auto using var_eq_dec. }
Defined.

Definition val_eqb (v1 v2 : val) : bool := if val_eq_dec v1 v2 then true else false.
Definition expr_eqb (e1 e2 : expr) : bool := if expr_eq_dec e1 e2 then true else false.

Module Coerce.
  Coercion BVar : var >-> binder.
  Coercion VBool : bool >-> val.
  Coercion VInt : Z >-> val.
  Coercion VLoc : loc >-> val.
  Coercion AVal : val >-> atom.
  Coercion AVar : var >-> atom.
  Coercion EAtom : atom >-> expr.
End Coerce.

Definition e1_binder (e : expr1) : binder := let (b, _) := e in b.
Definition e2_binder (e : expr2) : binder := let (b, _) := e in b.
Definition e1_expr (e : expr1) : expr := let (_, e') := e in e'.
Definition e2_expr1 (e : expr2) : expr1 := let (_, e') := e in e'.
