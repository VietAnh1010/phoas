From Stdlib Require Import Qcanon ZArith.
From shift_reset.core Require Import loc tag var.

Close Scope Qc_scope.

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
| TSeq : term -> term -> term
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
| TVVar : var -> val_term
| TVUnit : val_term
| TVInt : Z -> val_term
| TVFloat : Qc -> val_term
| TVNeg : val_term -> val_term
| TVAdd : val_term -> val_term -> val_term
| TVSub : val_term -> val_term -> val_term
| TVMul : val_term -> val_term -> val_term
| TVDiv : val_term -> val_term -> val_term
| TVMod : val_term -> val_term -> val_term
| TVBool : bool -> val_term
| TVNot : val_term -> val_term
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
| TVLt : val_term -> val_term -> val_term
| TVLe : val_term -> val_term -> val_term
| TVGt : val_term -> val_term -> val_term
| TVGe : val_term -> val_term -> val_term
| TVEq : val_term -> val_term -> val_term
| TVNeq : val_term -> val_term -> val_term
with term1 : Type :=
| T1 : binder -> term -> term1
with term2 : Type :=
| T2 : binder -> binder -> term -> term2
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
| VBool : bool -> val
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
