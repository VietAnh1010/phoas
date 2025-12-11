From Stdlib Require Import Ascii String Qcanon ZArith.
From shift_reset.core Require Import syntax loc.
From shift_reset.monad Require Import except.
From shift_reset.interpreter Require Import ierror.

Definition unwrap_vunit (v : val) : except exn unit :=
  match v with
  | VTt => pure tt
  | _ => throw (Type_error "unwrap_vunit")
  end.

Definition unwrap_vint (v : val) : except exn Z :=
  match v with
  | VInt z => pure z
  | _ => throw (Type_error "unwrap_vint")
  end.

Definition unwrap_vfloat (v : val) : except exn Qc :=
  match v with
  | VFloat q => pure q
  | _ => throw (Type_error "unwrap_vfloat")
  end.

Definition unwrap_vbool (v : val) : except exn bool :=
  match v with
  | VTrue => pure true
  | VFalse => pure false
  | _ => throw (Type_error "unwrap_vbool")
  end.

Definition unwrap_vchar (v : val) : except exn ascii :=
  match v with
  | VChar a => pure a
  | _ => throw (Type_error "unwrap_vchar")
  end.

Definition unwrap_vstring (v : val) : except exn string :=
  match v with
  | VString s => pure s
  | _ => throw (Type_error "unwrap_vstring")
  end.

Definition unwrap_vref (v : val) : except exn loc :=
  match v with
  | VRef l => pure l
  | _ => throw (Type_error "unwrap_vref")
  end.

Definition unwrap_vprod (v : val) : except exn (val * val) :=
  match v with
  | VPair v1 v2 => pure (v1, v2)
  | _ => throw (Type_error "unwrap_vprod")
  end.

Definition unwrap_vsum (v : val) : except exn (val + val) :=
  match v with
  | VInl v' => pure (inl v')
  | VInr v' => pure (inr v')
  | _ => throw (Type_error "unwrap_vsum")
  end.

Definition unwrap_vexn (v : val) : except exn exn :=
  match v with
  | VExn tag v' => pure (Exn tag v')
  | _ => throw (Type_error "unwrap_vexn")
  end.

Definition unwrap_veff (v : val) : except exn eff :=
  match v with
  | VEff tag v' => pure (Eff tag v')
  | _ => throw (Type_error "unwrap_veff")
  end.

Definition unwrap_vvariant (v : val) : except exn variant :=
  match v with
  | VVariant tag v' => pure (Variant tag v')
  | _ => throw (Type_error "unwrap_vvariant")
  end.

Definition unwrap_vtuple (v : val) : except exn tuple :=
  match v with
  | VTuple t => pure t
  | _ => throw (Type_error "unwrap_vtuple")
  end.

Definition unwrap_vrecord (v : val) : except exn record :=
  match v with
  | VRecord r => pure r
  | _ => throw (Type_error "unwrap_vrecord")
  end.

Definition unwrap_varray (v : val) : except exn array :=
  match v with
  | VArray l z => pure (Array l z)
  | _ => throw (Type_error "unwrap_varray")
  end.

Definition unwrap_vclosure (v : val) : except exn closure :=
  match v with
  | VFun b t e => pure (CFun b t e)
  | VFix f b t e => pure (CFix f b t e)
  | VFixMut t f e => pure (CFixMut t f e)
  | VMKPure mk => pure (CMKPure mk)
  | VMKReset mk => pure (CMKReset mk)
  | VMKHandle mk t1 t2 e => pure (CMKHandle mk t1 t2 e)
  | _ => throw (Type_error "unwrap_vclosure")
  end.
