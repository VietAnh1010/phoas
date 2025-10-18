From shift_reset.core Require Import syntax.

Fixpoint kont_append (k1 k2 : kont) : kont :=
  match k1 with
  | KNil => k2
  | KCons c k1' => KCons c (kont_append k1' k2)
  end.

Definition metakont_extend (mk : metakont) (k : kont) : metakont :=
  match mk with
  | MKPure k' => MKPure (kont_append k' k)
  | MKReset mk' k' => MKReset mk' (kont_append k' k)
  | MKPrompt mk' k' => MKPrompt mk' (kont_append k' k)
  | MKTry mk' c k' => MKTry mk' c (kont_append k' k)
  end.
