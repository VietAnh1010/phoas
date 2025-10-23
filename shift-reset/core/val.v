From shift_reset.core Require Import syntax tag.

Definition VFun' (t : term1) (env : env) : val := VFun (CFun env t).
Definition VFix' (t : term2) (env : env) : val := VFix (CFix env t).
Definition VExn' (tag : tag) (v : val) : val := VExn (Exn tag v).
Definition VEff' (tag : tag) (v : val) : val := VEff (Eff tag v).
