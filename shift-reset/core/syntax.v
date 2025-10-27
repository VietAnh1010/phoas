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

Inductive term : Type :=
| TVal : val_term -> term
| TApp : val_term -> val_term -> term
| TSeq : term -> term -> term
| TLet : term -> abs_term -> term
| TIf : val_term -> term -> term -> term
| TSplit : val_term -> abs2_term -> term
| TCase : val_term -> abs_term -> abs_term -> term
| TShift : tag -> abs_term -> term
| TReset : tag -> term -> term
| TControl : tag -> abs_term -> term
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
| TVTrue : val_term
| TVFalse : val_term
| TVNot : val_term -> val_term
| TVAnd : val_term -> val_term -> val_term
| TVOr : val_term -> val_term -> val_term
| TVFun : abs_term -> val_term
| TVFix : abs2_term -> val_term
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
with abs_term : Type :=
| TAbs : binder -> term -> abs_term
with abs2_term : Type :=
| TAbs2 : binder -> binder -> term -> abs2_term
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
| CFun : env -> abs_term -> fun_clo
with fix_clo : Type :=
| CFix : env -> abs2_term -> fix_clo
with kont_clo : Type :=
| CKSeq : env -> term -> kont_clo
| CKLet : env -> abs_term -> kont_clo
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
