From shift_reset.core Require Import syntax ident.

Definition fix_mut_defs_find_last (f : ident) : fix_mut_defs -> option (pattern * comp) :=
  let fix go o ds :=
    match ds with
    | FixMutNil => o
    | FixMutCons f' p c ds' => go (if ident_eqb f f' then Some (p, c) else o) ds'
    end
  in go None.
