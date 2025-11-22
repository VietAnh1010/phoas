From Stdlib Require Import Ascii String Qcanon ZArith.
From shift_reset.core Require Import syntax loc.
From shift_reset.interpreter Require Import ierror imonad.

Local Open Scope string_scope.

Definition unwrap_vunit (v : val) : imonad unit :=
  match v with
  | VTt => imonad_pure tt
  | _ => imonad_throw_error (Type_error "unwrap_vunit")
  end.

Definition unwrap_vint (v : val) : imonad Z :=
  match v with
  | VInt z => imonad_pure z
  | _ => imonad_throw_error (Type_error "unwrap_vint")
  end.

Definition unwrap_vfloat (v : val) : imonad Qc :=
  match v with
  | VFloat q => imonad_pure q
  | _ => imonad_throw_error (Type_error "unwrap_vfloat")
  end.

Definition unwrap_vbool (v : val) : imonad bool :=
  match v with
  | VTrue => imonad_pure true
  | VFalse => imonad_pure false
  | _ => imonad_throw_error (Type_error "unwrap_vbool")
  end.

Definition unwrap_vchar (v : val) : imonad ascii :=
  match v with
  | VChar a => imonad_pure a
  | _ => imonad_throw_error (Type_error "unwrap_vchar")
  end.

Definition unwrap_vstring (v : val) : imonad string :=
  match v with
  | VString s => imonad_pure s
  | _ => imonad_throw_error (Type_error "unwrap_vstring")
  end.

Definition unwrap_vref (v : val) : imonad loc :=
  match v with
  | VRef l => imonad_pure l
  | _ => imonad_throw_error (Type_error "unwrap_vref")
  end.

Definition unwrap_vprod (v : val) : imonad (val * val) :=
  match v with
  | VPair v1 v2 => imonad_pure (v1, v2)
  | _ => imonad_throw_error (Type_error "unwrap_vprod")
  end.

Definition unwrap_vsum (v : val) : imonad (val + val) :=
  match v with
  | VInl v' => imonad_pure (inl v')
  | VInr v' => imonad_pure (inr v')
  | _ => imonad_throw_error (Type_error "unwrap_vsum")
  end.

Definition unwrap_vexn (v : val) : imonad exn :=
  match v with
  | VExn tag v' => imonad_pure (Exn tag v')
  | _ => imonad_throw_error (Type_error "unwrap_vexn")
  end.

Definition unwrap_veff (v : val) : imonad eff :=
  match v with
  | VEff tag v' => imonad_pure (Eff tag v')
  | _ => imonad_throw_error (Type_error "unwrap_veff")
  end.

Definition unwrap_vvariant (v : val) : imonad variant :=
  match v with
  | VVariant tag v' => imonad_pure (Variant tag v')
  | _ => imonad_throw_error (Type_error "unwrap_vvariant")
  end.

Definition unwrap_vtuple (v : val) : imonad tuple :=
  match v with
  | VTuple t => imonad_pure t
  | _ => imonad_throw_error (Type_error "unwrap_vtuple")
  end.

Definition unwrap_vrecord (v : val) : imonad record :=
  match v with
  | VRecord r => imonad_pure r
  | _ => imonad_throw_error (Type_error "unwrap_vrecord")
  end.

Definition unwrap_varray (v : val) : imonad array :=
  match v with
  | VArray l z => imonad_pure (Array l z)
  | _ => imonad_throw_error (Type_error "unwrap_varray")
  end.

Definition unwrap_vclosure (v : val) : imonad closure :=
  match v with
  | VFun b t e => imonad_pure (CFun b t e)
  | VFix f b t e => imonad_pure (CFix f b t e)
  | VFixMut t f e => imonad_pure (CFixMut t f e)
  | VMKPure mk => imonad_pure (CMKPure mk)
  | VMKReset mk => imonad_pure (CMKReset mk)
  | VMKHandle mk t1 t2 e => imonad_pure (CMKHandle mk t1 t2 e)
  | _ => imonad_throw_error (Type_error "unwrap_vclosure")
  end.
