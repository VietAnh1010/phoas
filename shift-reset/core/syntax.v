From Stdlib Require Import Ascii String Qcanon ZArith.
From shift_reset.core Require Import loc tag var.

Inductive binder : Type :=
| BAny : binder
| BVar : var -> binder.

Inductive variant_pattern : Type :=
| PVariantAny : variant_pattern
| PVariantVar : var -> variant_pattern
| PVariantTag : tag -> binder -> variant_pattern.

Inductive tuple_pattern : Type :=
| PTupleNil : tuple_pattern
| PTupleCons : binder -> tuple_pattern -> tuple_pattern.

Inductive record_pattern : Type :=
| PRecordAny : record_pattern
| PRecordVar : var -> record_pattern
| PRecordNil : record_pattern
| PRecordCons : tag -> binder -> record_pattern -> record_pattern.

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
| Op2App : op2
| Op2Lt : op2
| Op2Le : op2
| Op2Gt : op2
| Op2Ge : op2
| Op2Eq : op2
| Op2Neq : op2.

Inductive term : Type :=
| TVal : val_term -> term
| TApp : val_term -> val_term -> term
| TSeq : term -> term -> term
| TLet : binder -> term -> term -> term
| TIf : val_term -> term -> term -> term
| TSplit : binder -> binder -> val_term -> term -> term
| TCase : val_term -> binder -> term -> binder -> term -> term
| TWhile : val_term -> term -> term
| TLetFix : var -> binder -> term -> term -> term
| TLetFixMut : fix_mut_term -> term -> term
| TLetTuple : tuple_pattern -> val_term -> term -> term
| TLetRecord : record_pattern -> val_term -> term -> term
| TMatchVariant : val_term -> variant_term -> term
| TShift : binder -> term -> term
| TReset : term -> term
| TControl : binder -> term -> term
| TPrompt : term -> term
| TRaise : val_term -> term
| TTry : term -> exn_term -> term
| TPerform : val_term -> term
| THandle : term -> ret_term -> eff_term -> term
| TShallowHandle : term -> ret_term -> eff_term -> term
with val_term : Type :=
| TVVar : var -> val_term
| TVTt : val_term
| TVInt : Z -> val_term
| TVFloat : Qc -> val_term
| TVTrue : val_term
| TVFalse : val_term
| TVChar : ascii -> val_term
| TVString : string -> val_term
| TVAnd : val_term -> val_term -> val_term
| TVOr : val_term -> val_term -> val_term
| TVFun : binder -> term -> val_term
| TVFix : var -> binder -> term -> val_term
| TVFixMut : fix_mut_term -> var -> val_term
| TVPair : val_term -> val_term -> val_term
| TVFst : val_term -> val_term
| TVSnd : val_term -> val_term
| TVTuple : tuple_term -> val_term
| TVRecord : record_term -> val_term
| TVProj : val_term -> tag -> val_term
| TVInl : val_term -> val_term
| TVInr : val_term -> val_term
| TVVariant : tag -> val_term -> val_term
| TVRef : val_term -> val_term
| TVGet : val_term -> val_term
| TVSet : val_term -> val_term -> val_term
| TVGetAt : val_term -> val_term -> val_term
| TVSetAt : val_term -> val_term -> val_term -> val_term
| TVExn : tag -> val_term -> val_term
| TVEff : tag -> val_term -> val_term
| TVAssert : val_term -> val_term
| TVArray : tuple_term -> val_term
| TVOp1 : op1 -> val_term -> val_term
| TVOp2 : op2 -> val_term -> val_term -> val_term
| TVBuiltin1 : tag -> val_term -> val_term
| TVBuiltin2 : tag -> val_term -> val_term -> val_term
with ret_term : Type :=
| TRetNone : ret_term
| TRetSome : binder -> term -> ret_term
with exn_term : Type :=
| TExnLast : variant_pattern -> term -> exn_term
| TExnCons : variant_pattern -> term -> exn_term -> exn_term
with eff_term : Type :=
| TEffLast : variant_pattern -> binder -> term -> eff_term
| TEffCons : variant_pattern -> binder -> term -> eff_term -> eff_term
with variant_term : Type :=
| TVariantNil : variant_term
| TVariantCons : variant_pattern -> term -> variant_term -> variant_term
with tuple_term : Type :=
| TTupleNil : tuple_term
| TTupleCons : val_term -> tuple_term -> tuple_term
with record_term : Type :=
| TRecordNil : record_term
| TRecordCons : tag -> val_term -> record_term -> record_term
with fix_mut_term : Type :=
| TFixMutLast : var -> binder -> term -> fix_mut_term
| TFixMutCons : var -> binder -> term -> fix_mut_term -> fix_mut_term.

Inductive val : Type :=
| VTt : val
| VInt : Z -> val
| VFloat : Qc -> val
| VTrue : val
| VFalse : val
| VChar : ascii -> val
| VString : string -> val
| VFun : binder -> term -> env -> val
| VFix : var -> binder -> term -> env -> val
| VFixMut : fix_mut_term -> var -> env -> val
| VPair : val -> val -> val
| VTuple : tuple -> val
| VRecord : record -> val
| VInl : val -> val
| VInr : val -> val
| VVariant : tag -> val -> val
| VRef : loc -> val
| VExn : tag -> val -> val
| VEff : tag -> val -> val
| VMKPure : metakont -> val
| VMKReset : metakont -> val
| VMKHandle : metakont -> ret_term -> eff_term -> env -> val
| VArray : loc -> Z -> val
with kont : Type :=
| KNil : kont
| KSeq : term -> env -> kont -> kont
| KLet : binder -> term -> env -> kont -> kont
| KApp : kont -> kont -> kont
with metakont : Type :=
| MKPure : kont -> metakont
| MKReset : metakont -> kont -> metakont
| MKPrompt : metakont -> kont -> metakont
| MKTry : metakont -> exn_term -> env -> kont -> metakont
| MKHandle : metakont -> ret_term -> eff_term -> env -> kont -> metakont
| MKShallowHandle : metakont -> ret_term -> eff_term -> env -> kont -> metakont
with env : Type :=
| ENil : env
| ECons : var -> val -> env -> env
with tuple : Type :=
| TupleNil : tuple
| TupleCons : val -> tuple -> tuple
with record : Type :=
| RecordNil : record
| RecordCons : tag -> val -> record -> record.

Inductive closure : Type :=
| CFun : binder -> term -> env -> closure
| CFix : var -> binder -> term -> env -> closure
| CFixMut : fix_mut_term -> var -> env -> closure
| CMKPure : metakont -> closure
| CMKReset : metakont -> closure
| CMKHandle : metakont -> ret_term -> eff_term -> env -> closure.

Inductive variant : Type :=
| Variant : tag -> val -> variant.

Inductive exn : Type :=
| Exn : tag -> val -> exn.

Inductive eff : Type :=
| Eff : tag -> val -> eff.

Inductive array : Type :=
| Array : loc -> Z -> array.
