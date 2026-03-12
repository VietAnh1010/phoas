From Stdlib Require Import Ascii String Qcanon ZArith.
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

Definition VClosure (c : closure) : val :=
  match c with
  | CFun p t e => VFun p t e
  | CFix f p t e => VFix f p t e
  | CFixMut t f e => VFixMut t f e
  | CMKPure mk => VMKPure mk
  | CMKReset mk => VMKReset mk
  | CMKReset0 mk => VMKReset0 mk
  | CMKHandle mk t1 t2 e => VMKHandle mk t1 t2 e
  end.

Definition VVariant' (v : variant) : val :=
  let (l, v) := v in VVariant l v.

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

Definition val_to_tuple (v : val) : option tuple :=
  match v with
  | VTuple t => Some t
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

Definition val_to_closure (v : val) : option closure :=
  match v with
  | VFun p t e => Some (CFun p t e)
  | VFix f p t e => Some (CFix f p t e)
  | VFixMut t f e => Some (CFixMut t f e)
  | VMKPure mk => Some (CMKPure mk)
  | VMKReset mk => Some (CMKReset mk)
  | VMKReset0 mk => Some (CMKReset0 mk)
  | VMKHandle mk t1 t2 e => Some (CMKHandle mk t1 t2 e)
  | _ => None
  end.
