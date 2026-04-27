Local Open Scope type_scope.

Definition identity (A : Type) : Type := A.
Definition maybe_t (M : Type -> Type) (A : Type) : Type := M (option A).
Definition reader_t (R : Type) (M : Type -> Type) (A : Type) : Type := R -> M A.
Definition writer_t (W : Type) (M : Type -> Type) (A : Type) : Type := M (A * W).
Definition state_t (S : Type) (M : Type -> Type) (A : Type) : Type := S -> M (A * S).
Definition except_t (E : Type) (M : Type -> Type) (A : Type) : Type := M (E + A).
Definition cont_t (R : Type) (M : Type -> Type) (A : Type) : Type := (A -> M R) -> M R.
Definition select_t (R : Type) (M : Type -> Type) (A : Type) : Type := (A -> M R) -> M A.
Definition accum_t (W : Type) (M : Type -> Type) (A : Type) : Type := W -> M (A * W).
