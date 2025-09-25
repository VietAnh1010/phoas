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
| VFun : clo1 -> val
| VFix : clo2 -> val
| VPair : val -> val -> val
| VInl : val -> val
| VInr : val -> val
| VLoc : loc -> val
| VKont : kont -> val
with atom : Type :=
| AVal : val -> atom
| AVar : var -> atom
with term : Type :=
| TAtom : atom -> term
| TLet : term -> term1 -> term
| TIf : atom -> term -> term -> term
| TPrim1 : prim1 -> atom -> term
| TPrim2 : prim2 -> atom -> atom -> term
| TFun : term1 -> term
| TFix : term2 -> term
| TApp : atom -> atom -> term
| TPair : atom -> atom -> term
| TFst : atom -> term
| TSnd : atom -> term
| TInl : atom -> term
| TInr : atom -> term
| TCase : atom -> term1 -> term1 -> term
| TRef : atom -> term
| TGet : atom -> term
| TSet : atom -> atom -> term
| TFree : atom -> term
| TShift : term1 -> term
| TReset : term -> term
| TCont : term -> clo1 -> term
with term1 : Type :=
| T1 : binder -> term -> term1
with term2 : Type :=
| T2 : binder -> term1 -> term2
with clo1 : Type :=
| C1 : term1 -> env -> clo1
with clo2 : Type :=
| C2 : term2 -> env -> clo2
with kont : Type :=
| KNil : kont
| KCons : clo1 -> kont -> kont
with env : Type :=
| ENil : env
| ECons : var -> val -> env -> env.

Definition prim1_eq_dec : forall (p1 p2 : prim1), {p1 = p2} + {p1 <> p2}.
Proof. decide equality. Defined.

Definition prim2_eq_dec : forall (p1 p2 : prim2), {p1 = p2} + {p1 <> p2}.
Proof. decide equality. Defined.

Definition binder_eq_dec : forall (b1 b2 : binder), {b1 = b2} + {b1 <> b2}.
Proof. decide equality; auto using var_eq_dec. Defined.

Fixpoint val_eq_dec : forall (v1 v2 : val), {v1 = v2} + {v1 <> v2}
with atom_eq_dec : forall (a1 a2 : atom), {a1 = a2} + {a1 <> a2}
with term_eq_dec : forall (t1 t2 : term), {t1 = t2} + {t1 <> t2}
with term1_eq_dec : forall (t1 t2 : term1), {t1 = t2} + {t1 <> t2}
with term2_eq_dec : forall (t1 t2 : term2), {t1 = t2} + {t1 <> t2}
with clo1_eq_dec : forall (c1 c2 : clo1), {c1 = c2} + {c1 <> c2}
with clo2_eq_dec : forall (c1 c2 : clo2), {c1 = c2} + {c1 <> c2}
with kont_eq_dec : forall (k1 k2 : kont), {k1 = k2} + {k1 <> k2}
with env_eq_dec : forall (env1 env2 : env), {env1 = env2} + {env1 <> env2}.
Proof.
  { decide equality; auto using bool_dec, Z.eq_dec, loc_eq_dec. }
  { decide equality; auto using var_eq_dec. }
  { decide equality; auto using prim1_eq_dec, prim2_eq_dec. }
  { decide equality; auto using binder_eq_dec. }
  { decide equality; auto using binder_eq_dec. }
  { decide equality. }
  { decide equality. }
  { decide equality. }
  { decide equality; auto using var_eq_dec. }
Defined.

Definition val_eqb (v1 v2 : val) : bool := if val_eq_dec v1 v2 then true else false.
Definition term_eqb (t1 t2 : term) : bool := if term_eq_dec t1 t2 then true else false.

Module Coerce.
  Coercion BVar : var >-> binder.
  Coercion VBool : bool >-> val.
  Coercion VInt : Z >-> val.
  Coercion VLoc : loc >-> val.
  Coercion AVal : val >-> atom.
  Coercion AVar : var >-> atom.
  Coercion TAtom : atom >-> term.
End Coerce.
