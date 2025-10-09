From shift_reset.core Require Import syntax.

Fixpoint kont_append (k1 k2 : kont) : kont :=
  match k1 with
  | KNil => k2
  | KCons c k1' => KCons c (kont_append k1' k2)
  end.
