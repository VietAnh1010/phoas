Module Type Semigroup.
  Parameter t : Type.
  Parameter append : t -> t -> t.
End Semigroup.

Module Type Monoid.
  Include Semigroup.
  Parameter empty : t.
End Monoid.
