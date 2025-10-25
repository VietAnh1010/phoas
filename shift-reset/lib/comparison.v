Definition compare_ltb (c : comparison) : bool :=
  match c with
  | Lt => true
  | _ => false
  end.

Definition compare_leb (c : comparison) : bool :=
  match c with
  | Gt => false
  | _ => true
  end.

Definition compare_gtb (c : comparison) : bool :=
  match c with
  | Gt => true
  | _ => false
  end.

Definition compare_geb (c : comparison) : bool :=
  match c with
  | Lt => false
  | _ => true
  end.
