From shift_reset.core Require Import syntax tag.

Definition VFun' (t : term1) (env : env) : val := VFun (C1 env t).
Definition VFix' (t : term2) (env : env) : val := VFix (C2 env t).
Definition VExn' (tag : tag) (v : val) : val := VExn (Exn tag v).
Definition VEff' (tag : tag) (v : val) : val := VEff (Eff tag v).
