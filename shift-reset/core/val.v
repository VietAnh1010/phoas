From Stdlib Require Import Qcanon ZArith.
From shift_reset.core Require Import syntax tag.

Definition VFun' (t : term1) (env : env) : val :=
  VFun (CFun env t).

Definition VFix' (t : term2) (env : env) : val :=
  VFix (CFix env t).

Definition VExn' (tag : tag) (v : val) : val :=
  VExn (Exn tag v).

Definition VEff' (tag : tag) (v : val) : val :=
  VEff (Eff tag v).

Definition VBool (b : bool) : val :=
  if b then VTrue else VFalse.

Definition VProd (p : val * val) : val :=
  let (v1, v2) := p in VPair v1 v2.

Definition VSum (s : val + val) : val :=
  match s with
  | inl v => VInl v
  | inr v => VInr v
  end.

Definition VInt_by {A} (f : A -> Z) (x : A) : val :=
  VInt (f x).

Definition VFloat_by {A} (f : A -> Qc) (x : A) : val :=
  VFloat (f x).

Definition VBool_by {A} (f : A -> bool) (x : A) : val :=
  VBool (f x).

Definition VInt_by2 {A B} (f : A -> B -> Z) (x : A) (y : B) : val :=
  VInt (f x y).

Definition VFloat_by2 {A B} (f : A -> B -> Qc) (x : A) (y : B) : val :=
  VFloat (f x y).

Definition VBool_by2 {A B} (f : A -> B -> bool) (x : A) (y : B) : val :=
  VBool (f x y).
