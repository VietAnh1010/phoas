From Stdlib Require Import Ascii String Qcanon ZArith.
From shift_reset.core Require Import syntax ident.

Coercion Ident : string >-> ident.
Coercion BVar : ident >-> binder.
Coercion PVar : ident >-> pattern.
Coercion PInt : Z >-> pattern.
Coercion PFloat : Qc >-> pattern.
Coercion PChar : ascii >-> pattern.
Coercion TVVar : ident >-> val_term.
Coercion TVInt : Z >-> val_term.
Coercion TVFloat : Qc >-> val_term.
Coercion TVChar : ascii >-> val_term.
Coercion TVOp1 : op1 >-> Funclass.
Coercion TVOp2 : op2 >-> Funclass.
Coercion TVal : val_term >-> term.
