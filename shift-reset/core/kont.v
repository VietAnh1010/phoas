From shift_reset.core Require Import syntax.

Fixpoint kont_size_acc (k : kont) (acc : nat) : nat :=
  match k with
  | KNil => acc
  | KCons0 _ _ k' => S (kont_size_acc k' acc)
  | KCons1 _ _ _ k' => S (kont_size_acc k' acc)
  | KApp k1 k2 => kont_size_acc k1 (kont_size_acc k2 acc)
  end.

Fixpoint kont_size (k : kont) : nat :=
  match k with
  | KNil => O
  | KCons0 _ _ k' => S (kont_size k')
  | KCons1 _ _ _ k' => S (kont_size k')
  | KApp k1 k2 => kont_size_acc k1 (kont_size k2)
  end.

Fixpoint kont_flatten_app (k1 k2 : kont) : kont :=
  match k1 with
  | KNil => k2
  | KCons0 t e k1' => KCons0 t e (kont_flatten_app k1' k2)
  | KCons1 b t e k1' => KCons1 b t e (kont_flatten_app k1' k2)
  | KApp k11 k12 => kont_flatten_app k11 (kont_flatten_app k12 k2)
  end.

Fixpoint kont_flatten (k : kont) : kont :=
  match k with
  | KNil => KNil
  | KCons0 t e k' => KCons0 t e (kont_flatten k')
  | KCons1 b t e k' => KCons1 b t e (kont_flatten k')
  | KApp k1 k2 => kont_flatten_app k1 (kont_flatten k2)
  end.
