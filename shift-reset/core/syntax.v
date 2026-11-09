From Stdlib Require Import Ascii String Qcanon ZArith.
From shift_reset.core Require Import ident loc.

Inductive binder : Type :=
| BAny : binder
| BVar : ident -> binder.

Inductive pattern : Type :=
| PAny : pattern
| PVar : ident -> pattern
| PAlias : pattern -> ident -> pattern
| POr : pattern -> pattern -> pattern
| PTt : pattern
| PInt : Z -> pattern
| PFloat : Qc -> pattern
| PTrue : pattern
| PFalse : pattern
| PChar : ascii -> pattern
| PString : string -> pattern
| PPair : pattern -> pattern -> pattern
| PTuple : tuple_pattern -> pattern
| PRecord : record_pattern -> pattern
| PInl : pattern -> pattern
| PInr : pattern -> pattern
| PNil : pattern
| PCons : pattern -> pattern -> pattern
| PVariant : variant_pattern -> pattern
with tuple_pattern : Type :=
| PTupleNil : tuple_pattern
| PTupleCons : pattern -> tuple_pattern -> tuple_pattern
with record_pattern : Type :=
| PRecordNil : record_pattern
| PRecordRest : pattern -> record_pattern
| PRecordCons : ident -> pattern -> record_pattern -> record_pattern
| PRecordConsPun : ident -> record_pattern -> record_pattern
with variant_pattern : Type :=
| PVariantNone : ident -> variant_pattern
| PVariantSome : ident -> pattern -> variant_pattern.

Inductive un_op : Type :=
| UnOpNeg : un_op
| UnOpNot : un_op
| UnOpLnot : un_op
| UnOpLength : un_op.

Inductive bin_op : Type :=
| BinOpAdd : bin_op
| BinOpSub : bin_op
| BinOpMul : bin_op
| BinOpDiv : bin_op
| BinOpMod : bin_op
| BinOpPow : bin_op
| BinOpLand : bin_op
| BinOpLor : bin_op
| BinOpLxor : bin_op
| BinOpShiftl : bin_op
| BinOpShiftr : bin_op
| BinOpApp : bin_op
| BinOpLt : bin_op
| BinOpLe : bin_op
| BinOpGt : bin_op
| BinOpGe : bin_op
| BinOpEq : bin_op
| BinOpNeq : bin_op.

Inductive for_direction : Type :=
| Upto : for_direction
| Downto : for_direction.

Inductive comp : Type :=
| CReturn : expr -> comp
| CApp : expr -> expr -> comp
| CSeq : comp -> comp -> comp
| CLet : pattern -> comp -> comp -> comp
| CMatch : expr -> cases -> comp
| CIf : expr -> comp -> comp -> comp
| CWhile : expr -> comp -> comp
| CFor : binder -> expr -> for_direction -> expr -> comp -> comp
| CLetFix : ident -> pattern -> comp -> comp -> comp
| CLetFixMut : fix_mut_defs -> comp -> comp
| CShift : binder -> comp -> comp
| CControl : binder -> comp -> comp
| CReset : comp -> comp
| CPrompt : comp -> comp
| CRaise : expr -> comp
| CTry : comp -> cases -> comp
| CPerform : expr -> comp
| CHandle : comp -> handle_cases -> comp
| CShallowHandle : comp -> handle_cases -> comp
with expr : Type :=
| EVar : ident -> expr
| ETt : expr
| EInt : Z -> expr
| EFloat : Qc -> expr
| ETrue : expr
| EFalse : expr
| EChar : ascii -> expr
| EString : string -> expr
| EAnd : expr -> expr -> expr
| EOr : expr -> expr -> expr
| EFun : pattern -> comp -> expr
| EFix : ident -> pattern -> comp -> expr
| EFixMut : fix_mut_defs -> ident -> expr
| EPair : expr -> expr -> expr
| EFst : expr -> expr
| ESnd : expr -> expr
| ETuple : exprs -> expr
| ERecord : record_expr -> expr
| EProjTuple : expr -> nat -> expr
| EProjRecord : expr -> ident -> expr
| EUpdateRecord : expr -> record_expr -> expr
| EInl : expr -> expr
| EInr : expr -> expr
| ENil : expr
| ECons : expr -> expr -> expr
| EVariant : variant_expr -> expr
| ERef : expr -> expr
| EArray : exprs -> expr
| EGet : expr -> expr
| ESet : expr -> expr -> expr
| EGetAt : expr -> expr -> expr
| ESetAt : expr -> expr -> expr -> expr
| EUnOp : un_op -> expr -> expr
| EBinOp : bin_op -> expr -> expr -> expr
| EPrim : ident -> expr
| EBy : comp -> expr
with cases : Type :=
| CasesNil : cases
| CasesCons : pattern -> comp -> cases -> cases
with handle_cases : Type :=
| HandleCases : return_case -> effect_cases -> handle_cases
with effect_cases : Type :=
| EffectCasesNil : effect_cases
| EffectCasesCons : pattern -> binder -> comp -> effect_cases -> effect_cases
with return_case : Type :=
| ReturnCaseNone : return_case
| ReturnCaseSome : pattern -> comp -> return_case
with fix_mut_defs : Type :=
| FixMutLast : ident -> pattern -> comp -> fix_mut_defs
| FixMutCons : ident -> pattern -> comp -> fix_mut_defs -> fix_mut_defs
with exprs : Type :=
| EsNil : exprs
| EsCons : expr -> exprs -> exprs
with record_expr : Type :=
| ERecordNil : record_expr
| ERecordRest : expr -> record_expr
| ERecordCons : ident -> expr -> record_expr -> record_expr
| ERecordConsPun : ident -> record_expr -> record_expr
with variant_expr : Type :=
| EVariantNone : ident -> variant_expr
| EVariantSome : ident -> expr -> variant_expr.

Definition match_cases : Type := cases.
Definition try_cases : Type := cases.

Inductive val : Type :=
| VTt : val
| VInt : Z -> val
| VFloat : Qc -> val
| VTrue : val
| VFalse : val
| VChar : ascii -> val
| VString : string -> val
| VFun : pattern -> comp -> ident_val_assocs -> val
| VFix : ident -> pattern -> comp -> ident_val_assocs -> val
| VFixMut : fix_mut_defs -> ident -> ident_val_assocs -> val
| VPrim : ident -> val
| VPair : val -> val -> val
| VTuple : vals -> val
| VRecord : ident_val_assocs -> val
| VInl : val -> val
| VInr : val -> val
| VNil : val
| VCons : val -> val -> val
| VVariant : variant -> val
| VRef : loc -> val
| VArray : loc -> Z -> val
| VMKPure : metakont -> val
| VMKReset : metakont -> val
| VMKHandle : metakont -> handle_cases -> ident_val_assocs -> val
with kont : Type :=
| KNil : kont
| KConsSeq : comp -> ident_val_assocs -> kont -> kont
| KConsLet : pattern -> comp -> ident_val_assocs -> kont -> kont
| KApp : kont -> kont -> kont
with metakont : Type :=
| MKPure : kont -> metakont
| MKReset : metakont -> kont -> metakont
| MKPrompt : metakont -> kont -> metakont
| MKTry : metakont -> cases -> ident_val_assocs -> kont -> metakont
| MKHandle : metakont -> handle_cases -> ident_val_assocs -> kont -> metakont
| MKShallowHandle : metakont -> handle_cases -> ident_val_assocs -> kont -> metakont
with vals : Type :=
| VsNil : vals
| VsCons : val -> vals -> vals
with ident_val_assocs : Type :=
| IVAsNil : ident_val_assocs
| IVAsCons : ident -> val -> ident_val_assocs -> ident_val_assocs
with variant : Type :=
| VariantNone : ident -> variant
| VariantSome : ident -> val -> variant.

Definition env : Type := ident_val_assocs.
Definition record : Type := ident_val_assocs.

Inductive applicable : Type :=
| AFun : pattern -> comp -> ident_val_assocs -> applicable
| AFix : ident -> pattern -> comp -> ident_val_assocs -> applicable
| AFixMut : fix_mut_defs -> ident -> ident_val_assocs -> applicable
| APrim : ident -> applicable
| AMKPure : metakont -> applicable
| AMKReset : metakont -> applicable
| AMKHandle : metakont -> handle_cases -> ident_val_assocs -> applicable.

Inductive array : Type :=
| Array : loc -> Z -> array.
