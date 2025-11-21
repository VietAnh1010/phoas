From Stdlib Require Import String Qcanon ZArith.
From shift_reset.core Require Import syntax.

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
  | CFun b t e => VFun b t e
  | CFix f b t e => VFix f b t e
  | CFixMut t f e => VFixMut t f e
  | CMKPure mk => VMKPure mk
  | CMKReset mk => VMKReset mk
  | CMKHandle mk t1 t2 e => VMKHandle mk t1 t2 e
  end.

Definition VVariant' (v : variant) : val :=
  let (tag, v) := v in VVariant tag v.

Definition VExn' (e : exn) : val :=
  let (tag, v) := e in VExn tag v.

Definition VEff' (e : eff) : val :=
  let (tag, v) := e in VEff tag v.

Definition VInt_by {A} (f : A -> Z) (x : A) : val :=
  VInt (f x).

Definition VFloat_by {A} (f : A -> Qc) (x : A) : val :=
  VFloat (f x).

Definition VBool_by {A} (f : A -> bool) (x : A) : val :=
  VBool (f x).

Definition VString_by {A} (f : A -> string) (x : A) : val :=
  VString (f x).

Definition VInt_by2 {A B} (f : A -> B -> Z) (x : A) (y : B) : val :=
  VInt (f x y).

Definition VFloat_by2 {A B} (f : A -> B -> Qc) (x : A) (y : B) : val :=
  VFloat (f x y).

Definition VBool_by2 {A B} (f : A -> B -> bool) (x : A) (y : B) : val :=
  VBool (f x y).

Definition VString_by2 {A B} (f : A -> B -> string) (x : A) (y : B) : val :=
  VString (f x y).
