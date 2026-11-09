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
Coercion EOp1 : op1 >-> Funclass.
Coercion EOp2 : op2 >-> Funclass.
Coercion TVal : expr >-> comp.
