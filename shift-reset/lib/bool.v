Definition bool_ltb (b1 b2 : bool) : bool := negb b1 && b2.
Definition bool_leb (b1 b2 : bool) : bool := negb b1 || b2.
Definition bool_gtb (b1 b2 : bool) : bool := b1 && negb b2.
Definition bool_geb (b1 b2 : bool) : bool := b1 || negb b2.
