From Stdlib Require Import Ascii String Qcanon ZArith.
From shift_reset.core Require Import syntax ident.

Coercion Ident : string >-> ident.
Coercion BVar : ident >-> binder.
Coercion PVar : ident >-> pattern.
Coercion PInt : Z >-> pattern.
Coercion PFloat : Qc >-> pattern.
Coercion PChar : ascii >-> pattern.
Coercion EVar : ident >-> expr.
Coercion EInt : Z >-> expr.
Coercion EFloat : Qc >-> expr.
Coercion EChar : ascii >-> expr.
Coercion EUnOp : un_op >-> Funclass.
Coercion EBinOp : bin_op >-> Funclass.
Coercion CReturn : expr >-> comp.
