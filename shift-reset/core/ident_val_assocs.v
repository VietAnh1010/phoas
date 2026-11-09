From shift_reset.core Require Import syntax ident.

Fixpoint ident_val_assocs_length (ivs : ident_val_assocs) : nat :=
  match ivs with
  | IVAsNil => O
  | IVAsCons _ _ ivs' => S (ident_val_assocs_length ivs')
  end.

Fixpoint ident_val_assocs_find (x : ident) (ivs : ident_val_assocs) : option val :=
  match ivs with
  | IVAsNil => None
  | IVAsCons x' v ivs' => if ident_eqb x x' then Some v else ident_val_assocs_find x ivs'
  end.

Fixpoint ident_val_assocs_find_remove (x : ident) (ivs : ident_val_assocs) : option val * ident_val_assocs :=
  match ivs with
  | IVAsNil => (None, ivs)
  | IVAsCons x' v ivs' =>
      if ident_eqb x x' then (Some v, ivs')
      else let (o, ivs') := ident_val_assocs_find_remove x ivs' in (o, IVAsCons x' v ivs')
  end.

Fixpoint ident_val_assocs_replace (x : ident) (v : val) (ivs : ident_val_assocs) : option ident_val_assocs :=
  match ivs with
  | IVAsNil => None
  | IVAsCons x' v' ivs' =>
      if ident_eqb x x' then Some (IVAsCons x' v ivs')
      else option_map (IVAsCons x' v') (ident_val_assocs_replace x v ivs')
  end.
