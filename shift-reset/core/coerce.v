From Stdlib Require Import String Qcanon ZArith.
From shift_reset.core Require Import syntax tag var.

Coercion Tag : string >-> tag.
Coercion Var : string >-> var.
Coercion BVar : var >-> binder.
Coercion PVariantVar : var >-> variant_pattern.
Coercion PRecordVar : var >-> record_pattern.
Coercion TVVar : var >-> val_term.
Coercion TVInt : Z >-> val_term.
Coercion TVFloat : Qc >-> val_term.
Coercion TVOp1 : op1 >-> Funclass.
Coercion TVOp2 : op2 >-> Funclass.
Coercion TVal : val_term >-> term.
