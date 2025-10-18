From Stdlib Require Import Bool String ZArith.
From shift_reset.core Require Import ident loc.

Inductive prim1 : Type :=
| P1Not : prim1
| P1Neg : prim1.

Inductive prim2 : Type :=
| P2Add : prim2
| P2Sub : prim2
| P2Mul : prim2
| P2Div : prim2
| P2Rem : prim2
| P2Lt : prim2
| P2Le : prim2
| P2Gt : prim2
| P2Ge : prim2
| P2And : prim2
| P2Or : prim2
| P2Xor : prim2
| P2Eq : prim2
| P2Neq : prim2.

Inductive atom : Type :=
| AUnit : atom
| AInt : Z -> atom
| ABool : bool -> atom
| AVar : ident -> atom.

Inductive binder : Type :=
| BAny : binder
| BVar : ident -> binder.

Inductive exn_pattern : Type :=
| ExnPAny : exn_pattern
| ExnPVar : ident -> exn_pattern
| ExnPExn : ident -> ident -> exn_pattern.

Inductive term : Type :=
| TAtom : atom -> term
| TFun : term1 -> term
| TFix : term2 -> term
| TApp : atom -> atom -> term
| TLet : term -> term1 -> term
| TIf : atom -> term -> term -> term
| TPrim1 : prim1 -> atom -> term
| TPrim2 : prim2 -> atom -> atom -> term
| TPair : atom -> atom -> term
| TSplit : atom -> term2 -> term
| TInl : atom -> term
| TInr : atom -> term
| TCase : atom -> term1 -> term1 -> term
| TRef : atom -> term
| TGet : atom -> term
| TSet : atom -> atom -> term
| TFree : atom -> term
| TShift : term1 -> term
| TReset : term -> term
| TControl : term1 -> term
| TPrompt : term -> term
| TExn : ident -> atom -> term
| TRaise : atom -> term
| TTry : term -> exn_term -> term
with term1 : Type :=
| T1 : binder -> term -> term1
with term2 : Type :=
| T2 : binder -> binder -> term -> term2
with exn_term : Type :=
| ExnT : exn_pattern -> term -> exn_term.

Inductive val : Type :=
| VUnit : val
| VInt : Z -> val
| VBool : bool -> val
| VFun : clo1 -> val
| VFix : clo2 -> val
| VPair : val -> val -> val
| VInl : val -> val
| VInr : val -> val
| VLoc : loc -> val
| VKontS : kont2S -> val
| VKontC : kont2C -> val
| VExn : exn -> val
with clo1 : Type :=
| C1 : env -> term1 -> clo1
with clo2 : Type :=
| C2 : env -> term2 -> clo2
with exn_clo : Type :=
| ExnC : env -> exn_term -> exn_clo
with kont1 : Type :=
| K1Nil : kont1
| K1Cons : clo1 -> kont1 -> kont1
with kont2S : Type :=
| K2SPure : kont1 -> kont2S
| K2SPrompt : kont2S -> kont1 -> kont2S
| K2STry : kont2S -> exn_clo -> kont1 -> kont2S
with kont2C : Type :=
| K2CPure : kont1 -> kont2C
| K2CReset : kont2C -> kont1 -> kont2C
| K2CTry : kont2C -> exn_clo -> kont1 -> kont2C
with env : Type :=
| EnvNil : env
| EnvCons : ident -> val -> env -> env
with exn : Type :=
| Exn : ident -> val -> exn.

Create HintDb eq_dec_db discriminated.

Hint Resolve Z.eq_dec : eq_dec_db.
Hint Resolve bool_dec : eq_dec_db.
Hint Resolve ident_eq_dec : eq_dec_db.
Hint Resolve loc_eq_dec : eq_dec_db.

Definition prim1_eq_dec : forall (p1 p2 : prim1), {p1 = p2} + {p1 <> p2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Definition prim2_eq_dec : forall (p1 p2 : prim2), {p1 = p2} + {p1 <> p2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Definition atom_eq_dec : forall (a1 a2 : atom), {a1 = a2} + {a1 <> a2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Definition binder_eq_dec : forall (b1 b2 : binder), {b1 = b2} + {b1 <> b2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Definition exn_pattern_eq_dec : forall (p1 p2 : exn_pattern), {p1 = p2} + {p1 <> p2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Hint Resolve prim1_eq_dec : eq_dec_db.
Hint Resolve prim2_eq_dec : eq_dec_db.
Hint Resolve atom_eq_dec : eq_dec_db.
Hint Resolve binder_eq_dec : eq_dec_db.
Hint Resolve exn_pattern_eq_dec : eq_dec_db.

Fixpoint term_eq_dec : forall (t1 t2 : term), {t1 = t2} + {t1 <> t2}
with term1_eq_dec : forall (t1 t2 : term1), {t1 = t2} + {t1 <> t2}
with term2_eq_dec : forall (t1 t2 : term2), {t1 = t2} + {t1 <> t2}
with exn_term_eq_dec : forall (t1 t2 : exn_term), {t1 = t2} + {t1 <> t2}.
Proof. all: decide equality; auto with eq_dec_db. Defined.

Hint Resolve term_eq_dec : eq_dec_db.
Hint Resolve term1_eq_dec : eq_dec_db.
Hint Resolve term2_eq_dec : eq_dec_db.
Hint Resolve exn_term_eq_dec : eq_dec_db.

Fixpoint val_eq_dec : forall (v1 v2 : val), {v1 = v2} + {v1 <> v2}
with clo1_eq_dec : forall (c1 c2 : clo1), {c1 = c2} + {c1 <> c2}
with clo2_eq_dec : forall (c1 c2 : clo2), {c1 = c2} + {c1 <> c2}
with exn_clo_eq_dec : forall (c1 c2 : exn_clo), {c1 = c2} + {c1 <> c2}
with kont1_eq_dec : forall (k1 k2 : kont1), {k1 = k2} + {k1 <> k2}
with kont2S_eq_dec : forall (ks1 ks2 : kont2S), {ks1 = ks2} + {ks1 <> ks2}
with kont2C_eq_dec : forall (kc1 kc2 : kont2C), {kc1 = kc2} + {kc1 <> kc2}
with env_eq_dec : forall (env1 env2 : env), {env1 = env2} + {env1 <> env2}
with exn_eq_dec : forall (exn1 exn2 : exn), {exn1 = exn2} + {exn1 <> exn2}.
Proof. all: decide equality; auto with eq_dec_db. Defined.

Hint Resolve val_eq_dec : eq_dec_db.
Hint Resolve clo1_eq_dec : eq_dec_db.
Hint Resolve clo2_eq_dec : eq_dec_db.
Hint Resolve exn_clo_eq_dec : eq_dec_db.
Hint Resolve kont1_eq_dec : eq_dec_db.
Hint Resolve kont2S_eq_dec : eq_dec_db.
Hint Resolve kont2C_eq_dec : eq_dec_db.
Hint Resolve env_eq_dec : eq_dec_db.
Hint Resolve exn_eq_dec : eq_dec_db.

Definition val_eqb (v1 v2 : val) : bool := if val_eq_dec v1 v2 then true else false.
Definition val_neqb (v1 v2 : val) : bool := if val_eq_dec v1 v2 then false else true.

Module Coerce.
  Coercion Ident : string >-> ident.
  Coercion BVar : ident >-> binder.
  Coercion AInt : Z >-> atom.
  Coercion ABool : bool >-> atom.
  Coercion AVar : ident >-> atom.
  Coercion TAtom : atom >-> term.
End Coerce.
