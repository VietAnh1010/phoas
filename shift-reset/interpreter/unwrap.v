From Stdlib Require Import String Qcanon ZArith.
From shift_reset.core Require Import syntax loc tag.
From shift_reset.interpreter Require Import ierror imonad.

Local Open Scope string_scope.
Local Unset Elimination Schemes.

Inductive lambda : Type :=
| LFun : fun_clo -> lambda
| LFix : fix_clo -> lambda
| LMKPure : metakont -> lambda
| LMKReset : metakont -> tag -> lambda
| LMKHandle : metakont -> handle_clo -> lambda.

Definition unwrap_vunit (v : val) : imonad unit :=
  match v with
  | VUnit => imonad_pure tt
  | _ => imonad_throw_error (Type_error "")
  end.

Definition unwrap_vint (v : val) : imonad Z :=
  match v with
  | VInt z => imonad_pure z
  | _ => imonad_throw_error (Type_error "")
  end.

Definition unwrap_vfloat (v : val) : imonad Qc :=
  match v with
  | VFloat q => imonad_pure q
  | _ => imonad_throw_error (Type_error "")
  end.

Definition unwrap_vbool (v : val) : imonad bool :=
  match v with
  | VTrue => imonad_pure true
  | VFalse => imonad_pure false
  | _ => imonad_throw_error (Type_error "")
  end.

Definition unwrap_vref (v : val) : imonad loc :=
  match v with
  | VRef l => imonad_pure l
  | _ => imonad_throw_error (Type_error "")
  end.

Definition unwrap_vprod (v : val) : imonad (val * val) :=
  match v with
  | VPair v1 v2 => imonad_pure (v1, v2)
  | _ => imonad_throw_error (Type_error "")
  end.

Definition unwrap_vsum (v : val) : imonad (val + val) :=
  match v with
  | VInl v' => imonad_pure (inl v')
  | VInr v' => imonad_pure (inr v')
  | _ => imonad_throw_error (Type_error "")
  end.

Definition unwrap_vexn (v : val) : imonad exn :=
  match v with
  | VExn exn => imonad_pure exn
  | _ => imonad_throw_error (Type_error "")
  end.

Definition unwrap_veff (v : val) : imonad eff :=
  match v with
  | VEff eff => imonad_pure eff
  | _ => imonad_throw_error (Type_error "")
  end.

Definition unwrap_vlambda (v : val) : imonad lambda :=
  match v with
  | VFun c => imonad_pure (LFun c)
  | VFix c => imonad_pure (LFix c)
  | VMKPure mk => imonad_pure (LMKPure mk)
  | VMKReset mk tag => imonad_pure (LMKReset mk tag)
  | VMKHandle mk c => imonad_pure (LMKHandle mk c)
  | _ => imonad_throw_error (Type_error "")
  end.
