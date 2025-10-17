From shift_reset.core Require Import syntax.

Fixpoint kont1_append (k1 k2 : kont1) : kont1 :=
  match k1 with
  | K1Nil => k2
  | K1Cons c k1' => K1Cons c (kont1_append k1' k2)
  end.

Definition kont2C_extend (kc : kont2C) (k : kont1) : kont2C :=
  match kc with
  | K2CHead k' => K2CHead (kont1_append k' k)
  | K2CSnoc kc' k' => K2CSnoc kc' (kont1_append k' k)
  end.
