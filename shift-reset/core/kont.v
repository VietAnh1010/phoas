From shift_reset.core Require Import syntax.

Fixpoint kont_length_add (k : kont) (n : nat) : nat :=
  match k with
  | KNil => n
  | KConsSeq _ _ k'
  | KConsLet _ _ _ k' => S (kont_length_add k' n)
  | KApp k1 k2 => kont_length_add k1 (kont_length_add k2 n)
  end.

Fixpoint kont_length (k : kont) : nat :=
  match k with
  | KNil => O
  | KConsSeq _ _ k'
  | KConsLet _ _ _ k' => S (kont_length k')
  | KApp k1 k2 => kont_length_add k1 (kont_length k2)
  end.

Fixpoint kont_flatten_append (k1 k2 : kont) : kont :=
  match k1 with
  | KNil => k2
  | KConsSeq t e k1' => KConsSeq t e (kont_flatten_append k1' k2)
  | KConsLet p t e k1' => KConsLet p t e (kont_flatten_append k1' k2)
  | KApp k11 k12 => kont_flatten_append k11 (kont_flatten_append k12 k2)
  end.

Fixpoint kont_flatten (k : kont) : kont :=
  match k with
  | KNil => KNil
  | KConsSeq t e k' => KConsSeq t e (kont_flatten k')
  | KConsLet p t e k' => KConsLet p t e (kont_flatten k')
  | KApp k1 k2 => kont_flatten_append k1 (kont_flatten k2)
  end.
