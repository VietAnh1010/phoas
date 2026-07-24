From Stdlib Require Import String.
From shift_reset.core Require Import syntax.

Fixpoint type_of_pattern (p : pattern) : string :=
  match p with
  | PAny | PVar _ => "<val>"
  | PAlias p' _ | POr p' _ => type_of_pattern p'
  | PTt => "unit"
  | PInt _ => "int"
  | PFloat _ => "float"
  | PTrue | PFalse => "bool"
  | PChar _ => "char"
  | PString _ => "string"
  | PPair _ _ => "prod"
  | PTuple _ => "tuple"
  | PRecord _ => "record"
  | PInl _ | PInr _ => "sum"
  | PVariant _ _ => "variant"
  end.
