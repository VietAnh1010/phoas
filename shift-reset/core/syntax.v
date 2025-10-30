From Stdlib Require Import Qcanon ZArith.
From shift_reset.core Require Import loc tag var.

Inductive binder : Type :=
| BAny : binder
| BVar : var -> binder.

Inductive pattern : Type :=
| PAny : pattern
| PVar : var -> pattern
| PConstr : tag -> binder -> pattern
| PAlias : pattern -> var -> pattern.

Inductive op1 : Type :=
| Op1Pos : op1
| Op1Neg : op1
| Op1Not : op1.

Inductive op2 : Type :=
| Op2Add : op2
| Op2Sub : op2
| Op2Mul : op2
| Op2Div : op2
| Op2Mod : op2
| Op2Ltb : op2
| Op2Leb : op2
| Op2Gtb : op2
| Op2Geb : op2
| Op2Eqb : op2
| Op2Neqb : op2.

Inductive term : Type :=
| TVal : val_term -> term
| TApp : val_term -> val_term -> term
| TSeq : term -> term -> term
| TLet : term -> term1 -> term
| TIf : val_term -> term -> term -> term
| TUnpair : val_term -> term2 -> term
| TCase : val_term -> term1 -> term1 -> term
| TWhile : val_term -> term -> term
| TShift : tag -> term1 -> term
| TReset : tag -> term -> term
| TControl : tag -> term1 -> term
| TPrompt : tag -> term -> term
| TRaise : val_term -> term
| TTry : term -> exn_term -> term
| TPerform : val_term -> term
| THandle : term -> ret_term -> eff_term -> term
| TShallowHandle : term -> ret_term -> eff_term -> term
with term1 : Type :=
| T1 : binder -> term -> term1
with term2 : Type :=
| T2 : binder -> binder -> term -> term2
with val_term : Type :=
| TVVar : var -> val_term
| TVUnit : val_term
| TVInt : Z -> val_term
| TVFloat : Qc -> val_term
| TVTrue : val_term
| TVFalse : val_term
| TVAnd : val_term -> val_term -> val_term
| TVOr : val_term -> val_term -> val_term
| TVFun : term1 -> val_term
| TVFix : term2 -> val_term
| TVPair : val_term -> val_term -> val_term
| TVInl : val_term -> val_term
| TVInr : val_term -> val_term
| TVRef : val_term -> val_term
| TVGet : val_term -> val_term
| TVSet : val_term -> val_term -> val_term
| TVFree : val_term -> val_term
| TVExn : tag -> val_term -> val_term
| TVEff : tag -> val_term -> val_term
| TVAssert : val_term -> val_term
| TVOp1 : op1 -> val_term -> val_term
| TVOp2 : op2 -> val_term -> val_term -> val_term
with ret_term : Type :=
| TRetNone : ret_term
| TRetSome : binder -> term -> ret_term
with exn_term : Type :=
| TExnLast : pattern -> term -> exn_term
| TExnCons : pattern -> term -> exn_term -> exn_term
with eff_term : Type :=
| TEffLast : pattern -> binder -> term -> eff_term
| TEffCons : pattern -> binder -> term -> eff_term -> eff_term.

Inductive val : Type :=
| VUnit : val
| VInt : Z -> val
| VFloat : Qc -> val
| VTrue : val
| VFalse : val
| VFun : fun_clo -> val
| VFix : fix_clo -> val
| VPair : val -> val -> val
| VInl : val -> val
| VInr : val -> val
| VRef : loc -> val
| VExn : exn -> val
| VEff : eff -> val
| VMKPure : metakont -> val
| VMKReset : metakont -> tag -> val
| VMKHandle : metakont -> handle_clo -> val
with fun_clo : Type :=
| CFun : env -> term1 -> fun_clo
with fix_clo : Type :=
| CFix : env -> term2 -> fix_clo
with kont_clo : Type :=
| CKSeq : env -> term -> kont_clo
| CKLet : env -> term1 -> kont_clo
with try_clo : Type :=
| CTry : env -> exn_term -> try_clo
with handle_clo : Type :=
| CHandle : env -> ret_term -> eff_term -> handle_clo
with shallow_handle_clo : Type :=
| CShallowHandle : env -> ret_term -> eff_term -> shallow_handle_clo
with kont : Type :=
| KNil : kont
| KCons : kont_clo -> kont -> kont
| KApp : kont -> kont -> kont
with metakont : Type :=
| MKPure : kont -> metakont
| MKReset : metakont -> tag -> kont -> metakont
| MKPrompt : metakont -> tag -> kont -> metakont
| MKTry : metakont -> try_clo -> kont -> metakont
| MKHandle : metakont -> handle_clo -> kont -> metakont
| MKShallowHandle : metakont -> shallow_handle_clo -> kont -> metakont
with env : Type :=
| EnvNil : env
| EnvCons : var -> val -> env -> env
with exn : Type :=
| Exn : tag -> val -> exn
with eff : Type :=
| Eff : tag -> val -> eff.
