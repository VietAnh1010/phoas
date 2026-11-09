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
| PRecordConsPun : ident -> record_pattern -> record_pattern
| PRecordCons : ident -> pattern -> record_pattern -> record_pattern
with variant_pattern : Type :=
| PVariantNone : ident -> variant_pattern
| PVariantSome : ident -> pattern -> variant_pattern.

Inductive op1 : Type :=
| Op1Neg : op1
| Op1Not : op1
| Op1Lnot : op1
| Op1Length : op1.

Inductive op2 : Type :=
| Op2Add : op2
| Op2Sub : op2
| Op2Mul : op2
| Op2Div : op2
| Op2Mod : op2
| Op2Pow : op2
| Op2Land : op2
| Op2Lor : op2
| Op2Lxor : op2
| Op2Shl : op2
| Op2Shr : op2
| Op2App : op2
| Op2Lt : op2
| Op2Le : op2
| Op2Gt : op2
| Op2Ge : op2
| Op2Eq : op2
| Op2Neq : op2.

Inductive for_direction : Type :=
| Upto : for_direction
| Downto : for_direction.

Inductive comp : Type :=
| TVal : expr -> comp
| CApp : expr -> expr -> comp
| CSeq : comp -> comp -> comp
| CLet : pattern -> comp -> comp -> comp
| CMatch : expr -> match_term -> comp
| CIf : expr -> comp -> comp -> comp
| CWhile : expr -> comp -> comp
| CFor : binder -> expr -> for_direction -> expr -> comp -> comp
| CLetFix : ident -> pattern -> comp -> comp -> comp
| CLetFixMut : fix_mut_term -> comp -> comp
| CShift : binder -> comp -> comp
| CControl : binder -> comp -> comp
| CReset : comp -> comp
| CPrompt : comp -> comp
| CRaise : expr -> comp
| CTry : comp -> exn_term -> comp
| CPerform : expr -> comp
| CHandle : comp -> ret_term -> eff_term -> comp
| CShallowHandle : comp -> ret_term -> eff_term -> comp
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
| EFixMut : fix_mut_term -> ident -> expr
| EPair : expr -> expr -> expr
| EFst : expr -> expr
| ESnd : expr -> expr
| ETuple : tuple_expr -> expr
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
| EArray : array_expr -> expr
| EGet : expr -> expr
| ESet : expr -> expr -> expr
| EGetAt : expr -> expr -> expr
| ESetAt : expr -> expr -> expr -> expr
| EOp1 : op1 -> expr -> expr
| EOp2 : op2 -> expr -> expr -> expr
| EPrim : ident -> expr
| EBy : comp -> expr
with match_term : Type :=
| TMatchNil : match_term
| TMatchCons : pattern -> comp -> match_term -> match_term
with fix_mut_term : Type :=
| TFixMutLast : ident -> pattern -> comp -> fix_mut_term
| TFixMutCons : ident -> pattern -> comp -> fix_mut_term -> fix_mut_term
with ret_term : Type :=
| TRetNone : ret_term
| TRetSome : pattern -> comp -> ret_term
with exn_term : Type :=
| TExnLast : pattern -> comp -> exn_term
| TExnCons : pattern -> comp -> exn_term -> exn_term
with eff_term : Type :=
| TEffLast : pattern -> binder -> comp -> eff_term
| TEffCons : pattern -> binder -> comp -> eff_term -> eff_term
with tuple_expr : Type :=
| ETupleNil : tuple_expr
| ETupleCons : expr -> tuple_expr -> tuple_expr
with record_expr : Type :=
| ERecordNil : record_expr
| ERecordRest : expr -> record_expr
| ERecordConsPun : ident -> record_expr -> record_expr
| ERecordCons : ident -> expr -> record_expr -> record_expr
with variant_expr : Type :=
| EVariantNone : ident -> variant_expr
| EVariantSome : ident -> expr -> variant_expr
with array_expr : Type :=
| EArrayNil : array_expr
| EArrayCons : expr -> array_expr -> array_expr.

Inductive val : Type :=
| VTt : val
| VInt : Z -> val
| VFloat : Qc -> val
| VTrue : val
| VFalse : val
| VChar : ascii -> val
| VString : string -> val
| VFun : pattern -> comp -> env -> val
| VFix : ident -> pattern -> comp -> env -> val
| VFixMut : fix_mut_term -> ident -> env -> val
| VPrim : ident -> val
| VPair : val -> val -> val
| VTuple : tuple -> val
| VRecord : record -> val
| VInl : val -> val
| VInr : val -> val
| VNil : val
| VCons : val -> val -> val
| VVariant : variant -> val
| VRef : loc -> val
| VArray : loc -> Z -> val
| VMKPure : metakont -> val
| VMKReset : metakont -> val
| VMKHandle : metakont -> ret_term -> eff_term -> env -> val
with kont : Type :=
| KNil : kont
| KConsSeq : comp -> env -> kont -> kont
| KConsLet : pattern -> comp -> env -> kont -> kont
| KApp : kont -> kont -> kont
with metakont : Type :=
| MKPure : kont -> metakont
| MKReset : metakont -> kont -> metakont
| MKPrompt : metakont -> kont -> metakont
| MKTry : metakont -> exn_term -> env -> kont -> metakont
| MKHandle : metakont -> ret_term -> eff_term -> env -> kont -> metakont
| MKShallowHandle : metakont -> ret_term -> eff_term -> env -> kont -> metakont
with env : Type :=
| EnvNil : env
| EnvCons : ident -> val -> env -> env
with tuple : Type :=
| TupleNil : tuple
| TupleCons : val -> tuple -> tuple
with record : Type :=
| RecordNil : record
| RecordCons : ident -> val -> record -> record
with variant : Type :=
| VariantNone : ident -> variant
| VariantSome : ident -> val -> variant.

Inductive applicable : Type :=
| AFun : pattern -> comp -> env -> applicable
| AFix : ident -> pattern -> comp -> env -> applicable
| AFixMut : fix_mut_term -> ident -> env -> applicable
| APrim : ident -> applicable
| AMKPure : metakont -> applicable
| AMKReset : metakont -> applicable
| AMKHandle : metakont -> ret_term -> eff_term -> env -> applicable.

Inductive array : Type :=
| Array : loc -> Z -> array.
