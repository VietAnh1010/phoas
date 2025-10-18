From shift_reset.core Require Import syntax.

Fixpoint kont1_append (k1 k2 : kont1) : kont1 :=
  match k1 with
  | K1Nil => k2
  | K1Cons c k1' => K1Cons c (kont1_append k1' k2)
  end.

Definition kont2C_extend (kc : kont2C) (k : kont1) : kont2C :=
  match kc with
  | K2CPure k' => K2CPure (kont1_append k' k)
  | K2CReset kc' k' => K2CReset kc' (kont1_append k' k)
  | K2CTry kc' c k' => K2CTry kc' c (kont1_append k' k)
  end.
