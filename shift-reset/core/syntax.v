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
| PVariant : ident -> pattern -> pattern
with tuple_pattern : Type :=
| PTupleNil : tuple_pattern
| PTupleCons : pattern -> tuple_pattern -> tuple_pattern
with record_pattern : Type :=
| PRecordNil : record_pattern
| PRecordAny : record_pattern
| PRecordRest : ident -> record_pattern
| PRecordCons0 : ident -> record_pattern -> record_pattern
| PRecordCons1 : ident -> pattern -> record_pattern -> record_pattern.

(*
Inductive variant_pattern : Type :=
| PVariantBind : binder -> variant_pattern
| PVariantConstr : ident -> binder -> variant_pattern.

Inductive tuple_pattern : Type :=
| PTupleNil : tuple_pattern
| PTupleRest : binder -> tuple_pattern
| PTupleCons : binder -> tuple_pattern -> tuple_pattern.

Inductive record_pattern : Type :=
| PRecordNil : record_pattern
| PRecordRest : binder -> record_pattern
| PRecordCons0 : ident -> record_pattern -> record_pattern
| PRecordCons1 : ident -> binder -> record_pattern -> record_pattern.
 *)

Inductive op1 : Type :=
| Op1Pos : op1
| Op1Neg : op1
| Op1Not : op1
| Op1Lnot : op1.

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

Inductive term : Type :=
| TVal : val_term -> term
| TApp : val_term -> val_term -> term
| TSeq : term -> term -> term
| TLet : pattern -> term -> term -> term
| TMatch : term -> match_term -> term
| TIf : val_term -> term -> term -> term
| TWhile : val_term -> term -> term
| TFor : binder -> val_term -> for_direction -> val_term -> term -> term
| TLetFix : ident -> pattern -> term -> term -> term
| TLetFixMut : fix_mut_term -> term -> term
| TShift : binder -> term -> term
| TControl : binder -> term -> term
| TShift0 : binder -> term -> term
| TControl0 : binder -> term -> term
| TReset : term -> term
| TPrompt : term -> term
| TReset0 : term -> term
| TPrompt0 : term -> term
| TRaise : val_term -> term
| TTry : term -> exn_term -> term
| TPerform : val_term -> term
| THandle : term -> ret_term -> eff_term -> term
| TShallowHandle : term -> ret_term -> eff_term -> term
with val_term : Type :=
| TVVar : ident -> val_term
| TVTt : val_term
| TVInt : Z -> val_term
| TVFloat : Qc -> val_term
| TVTrue : val_term
| TVFalse : val_term
| TVChar : ascii -> val_term
| TVString : string -> val_term
| TVAnd : val_term -> val_term -> val_term
| TVOr : val_term -> val_term -> val_term
| TVFun : pattern -> term -> val_term
| TVFix : ident -> pattern -> term -> val_term
| TVFixMut : fix_mut_term -> ident -> val_term
| TVPair : val_term -> val_term -> val_term
| TVFst : val_term -> val_term
| TVSnd : val_term -> val_term
| TVTuple : tuple_term -> val_term
| TVRecord : record_term -> val_term
| TVProjTuple : val_term -> nat -> val_term
| TVProjRecord : val_term -> ident -> val_term
| TVInl : val_term -> val_term
| TVInr : val_term -> val_term
| TVVariant : ident -> val_term -> val_term
| TVRef : val_term -> val_term
| TVArray : array_term -> val_term
| TVGet : val_term -> val_term
| TVSet : val_term -> val_term -> val_term
| TVGetAt : val_term -> val_term -> val_term
| TVSetAt : val_term -> val_term -> val_term -> val_term
| TVAssert : val_term -> val_term
| TVOp1 : op1 -> val_term -> val_term
| TVOp2 : op2 -> val_term -> val_term -> val_term
| TVBuiltin1 : ident -> val_term -> val_term
| TVBuiltin2 : ident -> val_term -> val_term -> val_term
| TVBy : term -> val_term
with ret_term : Type :=
| TRetNone : ret_term
| TRetSome : pattern -> term -> ret_term
with exn_term : Type :=
| TExnLast : pattern -> term -> exn_term
| TExnCons : pattern -> term -> exn_term -> exn_term
with eff_term : Type :=
| TEffLast : pattern -> binder -> term -> eff_term
| TEffCons : pattern -> binder -> term -> eff_term -> eff_term
with match_term : Type :=
| TMatchNil : match_term
| TMatchCons : pattern -> term -> match_term -> match_term
with tuple_term : Type :=
| TTupleNil : tuple_term
| TTupleCons : val_term -> tuple_term -> tuple_term
with record_term : Type :=
| TRecordNil : record_term
| TRecordRest : val_term -> record_term
| TRecordCons0 : ident -> record_term -> record_term
| TRecordCons1 : ident -> val_term -> record_term -> record_term
with fix_mut_term : Type :=
| TFixMutLast : ident -> pattern -> term -> fix_mut_term
| TFixMutCons : ident -> pattern -> term -> fix_mut_term -> fix_mut_term
with array_term : Type :=
| TArrayNil : array_term
| TArrayCons : val_term -> array_term -> array_term.

Inductive val : Type :=
| VTt : val
| VInt : Z -> val
| VFloat : Qc -> val
| VTrue : val
| VFalse : val
| VChar : ascii -> val
| VString : string -> val
| VFun : pattern -> term -> env -> val
| VFix : ident -> pattern -> term -> env -> val
| VFixMut : fix_mut_term -> ident -> env -> val
| VPair : val -> val -> val
| VTuple : tuple -> val
| VRecord : record -> val
| VInl : val -> val
| VInr : val -> val
| VVariant : ident -> val -> val
| VRef : loc -> val
| VArray : loc -> Z -> val
| VMKPure : metakont -> val
| VMKReset : metakont -> val
| VMKReset0 : metakont -> val
| VMKHandle : metakont -> ret_term -> eff_term -> env -> val
with kont : Type :=
| KNil : kont
| KCons0 : term -> env -> kont -> kont
| KCons1 : pattern -> term -> env -> kont -> kont
| KCons2 : match_term -> env -> kont -> kont
| KApp : kont -> kont -> kont
with metakont : Type :=
| MKPure : kont -> metakont
| MKReset : metakont -> kont -> metakont
| MKPrompt : metakont -> kont -> metakont
| MKReset0 : metakont -> kont -> metakont
| MKPrompt0 : metakont -> kont -> metakont
| MKTry : metakont -> exn_term -> env -> kont -> metakont
| MKHandle : metakont -> ret_term -> eff_term -> env -> kont -> metakont
| MKShallowHandle : metakont -> ret_term -> eff_term -> env -> kont -> metakont
with env : Type :=
| ENil : env
| ECons : ident -> val -> env -> env
with tuple : Type :=
| TupleNil : tuple
| TupleCons : val -> tuple -> tuple
with record : Type :=
| RecordNil : record
| RecordCons : ident -> val -> record -> record.

Inductive closure : Type :=
| CFun : pattern -> term -> env -> closure
| CFix : ident -> pattern -> term -> env -> closure
| CFixMut : fix_mut_term -> ident -> env -> closure
| CMKPure : metakont -> closure
| CMKReset : metakont -> closure
| CMKReset0 : metakont -> closure
| CMKHandle : metakont -> ret_term -> eff_term -> env -> closure.

Inductive variant : Type :=
| Variant : ident -> val -> variant.

Inductive array : Type :=
| Array : loc -> Z -> array.
