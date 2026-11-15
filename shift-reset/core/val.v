From Stdlib Require Import Ascii String Qcanon ZArith.
From shift_reset.lib Require option.
From shift_reset.core Require Import syntax loc.

Definition VBool (b : bool) : val :=
  if b then VTrue else VFalse.

Definition VProd (p : val * val) : val :=
  let (v1, v2) := p in VPair v1 v2.

Definition VSum (s : val + val) : val :=
  match s with
  | inl v => VInl v
  | inr v => VInr v
  end.

Definition VApplicable (a : applicable) : val :=
  match a with
  | AFun p c e => VFun p c e
  | AFix f p c e => VFix f p c e
  | AFixMut ds f e => VFixMut ds f e
  | APrim l => VPrim l
  | AMKPure mk => VMKPure mk
  | AMKReset mk => VMKReset mk
  | AMKHandle mk cs e => VMKHandle mk cs e
  end.

Definition val_to_unit (v : val) : option unit :=
  match v with
  | VTt => Some tt
  | _ => None
  end.

Definition val_to_int (v : val) : option Z :=
  match v with
  | VInt z => Some z
  | _ => None
  end.

Definition val_to_float (v : val) : option Qc :=
  match v with
  | VFloat q => Some q
  | _ => None
  end.

Definition val_to_bool (v : val) : option bool :=
  match v with
  | VTrue => Some true
  | VFalse => Some false
  | _ => None
  end.

Definition val_to_char (v : val) : option ascii :=
  match v with
  | VChar a => Some a
  | _ => None
  end.

Definition val_to_string (v : val) : option string :=
  match v with
  | VString s => Some s
  | _ => None
  end.

Definition val_to_ref (v : val) : option loc :=
  match v with
  | VRef l => Some l
  | _ => None
  end.

Definition val_to_prod (v : val) : option (val * val) :=
  match v with
  | VPair v1 v2 => Some (v1, v2)
  | _ => None
  end.

Definition val_to_sum (v : val) : option (val + val) :=
  match v with
  | VInl v' => Some (inl v')
  | VInr v' => Some (inr v')
  | _ => None
  end.

Definition val_to_variant (v : val) : option variant :=
  match v with
  | VVariant l v' => Some (Variant l v')
  | _ => None
  end.

Definition val_to_enum (v : val) : option enum :=
  match v with
  | VEnum l => Some (Enum l)
  | _ => None
  end.

Definition val_to_tuple (v : val) : option tuple :=
  match v with
  | VTuple vs => Some (Tuple vs)
  | _ => None
  end.

Definition val_to_record (v : val) : option record :=
  match v with
  | VRecord r => Some r
  | _ => None
  end.

Definition val_to_array (v : val) : option array :=
  match v with
  | VArray l z => Some (Array l z)
  | _ => None
  end.

Definition val_to_applicable (v : val) : option applicable :=
  match v with
  | VFun p c e => Some (AFun p c e)
  | VFix f p c e => Some (AFix f p c e)
  | VFixMut ds f e => Some (AFixMut ds f e)
  | VPrim l => Some (APrim l)
  | VMKPure mk => Some (AMKPure mk)
  | VMKReset mk => Some (AMKReset mk)
  | VMKHandle mk cs e => Some (AMKHandle mk cs e)
  | _ => None
  end.

Definition val_is_applicable (v : val) : bool :=
  option.is_some (val_to_applicable v).

Definition type_of_val (v : val) : string :=
  match v with
  | VTt => "unit"
  | VInt _ => "int"
  | VFloat _ => "float"
  | VTrue | VFalse => "bool"
  | VChar _ => "char"
  | VString _ => "string"
  | VPair _ _ => "prod"
  | VTuple _ => "tuple"
  | VRecord _ => "record"
  | VInl _ | VInr _ => "sum"
  | VVariant _ _ => "variant"
  | VEnum _ => "enum"
  | VNil | VCons _ _ => "list"
  | VRef _ => "ref"
  | VArray _ _ => "array"
  | VFun _ _ _
  | VFix _ _ _ _
  | VFixMut _ _ _
  | VPrim _
  | VMKPure _
  | VMKReset _
  | VMKHandle _ _ _ => "applicable"
  end.
