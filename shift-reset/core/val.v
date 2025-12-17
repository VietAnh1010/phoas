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
  | CMKReset0 mk => VMKReset0 mk
  | CMKHandle mk t1 t2 e => VMKHandle mk t1 t2 e
  end.

Definition VVariant' (v : variant) : val :=
  let (l, v) := v in VVariant l v.

Definition VExn' (x : exn) : val :=
  let (l, v) := x in VExn l v.

Definition VEff' (f : eff) : val :=
  let (l, v) := f in VEff l v.
