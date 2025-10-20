From Stdlib Require Import Bool String ZArith.
From shift_reset.core Require Import loc tag var.

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
| AVar : var -> atom.

Inductive binder : Type :=
| BAny : binder
| BVar : var -> binder.

Inductive pattern : Type :=
| PAny : pattern
| PVar : var -> pattern
| PConstr : tag -> binder -> pattern
| PAlias : pattern -> var -> pattern.

Inductive term : Type :=
| TVal : val_term -> term
| TApp : val_term -> val_term -> term
| TLet : term -> term1 -> term
| TIf : val_term -> term -> term -> term
| TSplit : val_term -> term2 -> term
| TCase : val_term -> term1 -> term1 -> term
| TShift : tag -> term1 -> term
| TReset : tag -> term -> term
| TControl : tag -> term1 -> term
| TPrompt : tag -> term -> term
| TRaise : val_term -> term
| TTry : term -> exn_term -> term
| TPerform : val_term -> term
| THandle : term -> ret_term -> eff_term -> term
| TShallowHandle : term -> ret_term -> eff_term -> term
with val_term : Type :=
| TVAtom : atom -> val_term
| TVFun : term1 -> val_term
| TVFix : term2 -> val_term
| TVPrim1 : prim1 -> val_term -> val_term
| TVPrim2 : prim2 -> val_term -> val_term -> val_term
| TVPair : val_term -> val_term -> val_term
| TVInl : val_term -> val_term
| TVInr : val_term -> val_term
| TVRef : val_term -> val_term
| TVGet : val_term -> val_term
| TVSet : val_term -> val_term -> val_term
| TVFree : val_term -> val_term
| TVExn : tag -> val_term -> val_term
| TVEff : tag -> val_term -> val_term
with term1 : Type :=
| T1 : binder -> term -> term1
with term2 : Type :=
| T2 : binder -> binder -> term -> term2
with ret_term : Type :=
| TRet0 : ret_term
| TRet1 : binder -> term -> ret_term
with exn_term : Type :=
| TExnBase : pattern -> term -> exn_term
| TExnCons : pattern -> term -> exn_term -> exn_term
with eff_term : Type :=
| TEffBase : pattern -> binder -> term -> eff_term
| TEffCons : pattern -> binder -> term -> eff_term -> eff_term.

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
| VKontReset : metakont -> tag -> val
| VKont : metakont -> val
| VKontHandle : metakont -> handle_clo -> val
| VExn : exn -> val
| VEff : eff -> val
with clo1 : Type :=
| C1 : env -> term1 -> clo1
with clo2 : Type :=
| C2 : env -> term2 -> clo2
with try_clo : Type :=
| CTry : env -> exn_term -> try_clo
with handle_clo : Type :=
| CHandle : env -> ret_term -> eff_term -> handle_clo
with kont : Type :=
| KNil : kont
| KCons : clo1 -> kont -> kont
with metakont : Type :=
| MKPure : kont -> metakont
| MKReset : metakont -> tag -> kont -> metakont
| MKPrompt : metakont -> tag -> kont -> metakont
| MKTry : metakont -> try_clo -> kont -> metakont
| MKHandle : metakont -> handle_clo -> kont -> metakont
| MKShallowHandle : metakont -> handle_clo -> kont -> metakont
with env : Type :=
| EnvNil : env
| EnvCons : var -> val -> env -> env
with exn : Type :=
| Exn : tag -> val -> exn
with eff : Type :=
| Eff : tag -> val -> eff.

Create HintDb eq_dec_db discriminated.

Hint Resolve Z.eq_dec : eq_dec_db.
Hint Resolve bool_dec : eq_dec_db.
Hint Resolve loc_eq_dec : eq_dec_db.
Hint Resolve tag_eq_dec : eq_dec_db.
Hint Resolve var_eq_dec : eq_dec_db.

Definition prim1_eq_dec : forall (p1 p2 : prim1), {p1 = p2} + {p1 <> p2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Definition prim2_eq_dec : forall (p1 p2 : prim2), {p1 = p2} + {p1 <> p2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Definition atom_eq_dec : forall (a1 a2 : atom), {a1 = a2} + {a1 <> a2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Definition binder_eq_dec : forall (b1 b2 : binder), {b1 = b2} + {b1 <> b2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Hint Resolve prim1_eq_dec : eq_dec_db.
Hint Resolve prim2_eq_dec : eq_dec_db.
Hint Resolve atom_eq_dec : eq_dec_db.
Hint Resolve binder_eq_dec : eq_dec_db.

Definition pattern_eq_dec : forall (p1 p2 : pattern), {p1 = p2} + {p1 <> p2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Hint Resolve pattern_eq_dec : eq_dec_db.

Fixpoint term_eq_dec : forall (t1 t2 : term), {t1 = t2} + {t1 <> t2}
with val_term_eq_dec : forall (t1 t2 : val_term), {t1 = t2} + {t1 <> t2}
with term1_eq_dec : forall (t1 t2 : term1), {t1 = t2} + {t1 <> t2}
with term2_eq_dec : forall (t1 t2 : term2), {t1 = t2} + {t1 <> t2}
with ret_term_eq_dec : forall (t1 t2 : ret_term), {t1 = t2} + {t1 <> t2}
with exn_term_eq_dec : forall (t1 t2 : exn_term), {t1 = t2} + {t1 <> t2}
with eff_term_eq_dec : forall (t1 t2 : eff_term), {t1 = t2} + {t1 <> t2}.
Proof. all: decide equality; auto with eq_dec_db. Defined.

Hint Resolve term_eq_dec : eq_dec_db.
Hint Resolve val_term_eq_dec : eq_dec_db.
Hint Resolve term1_eq_dec : eq_dec_db.
Hint Resolve term2_eq_dec : eq_dec_db.
Hint Resolve ret_term_eq_dec : eq_dec_db.
Hint Resolve exn_term_eq_dec : eq_dec_db.
Hint Resolve eff_term_eq_dec : eq_dec_db.

Fixpoint val_eq_dec : forall (v1 v2 : val), {v1 = v2} + {v1 <> v2}
with clo1_eq_dec : forall (c1 c2 : clo1), {c1 = c2} + {c1 <> c2}
with clo2_eq_dec : forall (c1 c2 : clo2), {c1 = c2} + {c1 <> c2}
with try_clo_eq_dec : forall (c1 c2 : try_clo), {c1 = c2} + {c1 <> c2}
with handle_clo_eq_dec : forall (c1 c2 : handle_clo), {c1 = c2} + {c1 <> c2}
with kont_eq_dec : forall (k1 k2 : kont), {k1 = k2} + {k1 <> k2}
with metakont_eq_dec : forall (mk1 mk2 : metakont), {mk1 = mk2} + {mk1 <> mk2}
with env_eq_dec : forall (env1 env2 : env), {env1 = env2} + {env1 <> env2}
with exn_eq_dec : forall (exn1 exn2 : exn), {exn1 = exn2} + {exn1 <> exn2}
with eff_eq_dec : forall (eff1 eff2 : eff), {eff1 = eff2} + {eff1 <> eff2}.
Proof. all: decide equality; auto with eq_dec_db. Defined.

Hint Resolve val_eq_dec : eq_dec_db.
Hint Resolve clo1_eq_dec : eq_dec_db.
Hint Resolve clo2_eq_dec : eq_dec_db.
Hint Resolve try_clo_eq_dec : eq_dec_db.
Hint Resolve handle_clo_eq_dec : eq_dec_db.
Hint Resolve kont_eq_dec : eq_dec_db.
Hint Resolve metakont_eq_dec : eq_dec_db.
Hint Resolve env_eq_dec : eq_dec_db.
Hint Resolve exn_eq_dec : eq_dec_db.
Hint Resolve eff_eq_dec : eq_dec_db.

Definition val_eqb (v1 v2 : val) : bool := if val_eq_dec v1 v2 then true else false.
Definition val_neqb (v1 v2 : val) : bool := if val_eq_dec v1 v2 then false else true.

Module Coerce.
  Coercion Tag : string >-> tag.
  Coercion Var : string >-> var.
  Coercion BVar : var >-> binder.
  Coercion PVar : var >-> pattern.
  Coercion AInt : Z >-> atom.
  Coercion ABool : bool >-> atom.
  Coercion AVar : var >-> atom.
  Coercion TVAtom : atom >-> val_term.
  Coercion TVal : val_term >-> term.
End Coerce.
