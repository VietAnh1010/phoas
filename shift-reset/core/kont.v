From shift_reset.core Require Import syntax.

Fixpoint kont_length_add (k : kont) (n : nat) : nat :=
  match k with
  | KNil => n
  | KConsSeq _ _ k'
  | KConsLet _ _ _ k' => S (kont_length_add k' n)
  | KAppend k1 k2 => kont_length_add k1 (kont_length_add k2 n)
  end.

Fixpoint kont_length (k : kont) : nat :=
  match k with
  | KNil => O
  | KConsSeq _ _ k'
  | KConsLet _ _ _ k' => S (kont_length k')
  | KAppend k1 k2 => kont_length_add k1 (kont_length k2)
  end.

Fixpoint kont_flatten_append (k1 k2 : kont) : kont :=
  match k1 with
  | KNil => k2
  | KConsSeq c e k1' => KConsSeq c e (kont_flatten_append k1' k2)
  | KConsLet p c e k1' => KConsLet p c e (kont_flatten_append k1' k2)
  | KAppend k11 k12 => kont_flatten_append k11 (kont_flatten_append k12 k2)
  end.

Fixpoint kont_flatten (k : kont) : kont :=
  match k with
  | KNil => KNil
  | KConsSeq c e k' => KConsSeq c e (kont_flatten k')
  | KConsLet p c e k' => KConsLet p c e (kont_flatten k')
  | KAppend k1 k2 => kont_flatten_append k1 (kont_flatten k2)
  end.
