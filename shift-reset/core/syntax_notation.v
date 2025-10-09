From shift_reset.core Require Import syntax var.

Declare Scope term_scope.
Delimit Scope term_scope with term.
Bind Scope term_scope with term.
Open Scope term_scope.

Declare Custom Entry term.

Notation "<{ t }>" := t (t custom term at level 99) : term_scope.
Notation "( t )" := t (in custom term, t at level 99) : term_scope.
Notation "t" := t (in custom term at level 0, t constr at level 0) : term_scope.
Notation "{ t }" := t (in custom term, t constr) : term_scope.

Notation "a1 a2" :=
  (TApp a1 a2)
    (in custom term at level 10,
        a1 custom term,
        a2 custom term) : term_scope.

Notation "'if' a 'then' t1 'else' t2" :=
  (TIf a t1 t2)
    (in custom term at level 69,
        a custom term,
        t1 custom term,
        t2 custom term) : term_scope.

Notation "'let' x := t1 'in' t2" :=
  (TLet t1 (T1 x t2))
    (in custom term at level 69,
        x at level 0,
        t1 custom term,
        t2 custom term,
        right associativity) : term_scope.

Notation "'let' f x1 .. xn := t1 'in' t2" :=
  (TLet (TFun (T1 x1 .. (TFun (T1 xn t1)) ..)) (T1 f t2))
    (in custom term at level 69,
        f, x1, xn at level 0,
        t1 custom term,
        t2 custom term,
        right associativity) : term_scope.

Notation "'let' 'fix' f x := t1 'in' t2" :=
  (TLet (TFix (T2 f x t1)) (T1 f t2))
    (in custom term at level 69,
        f, x at level 0,
        t1 custom term,
        t2 custom term,
        right associativity) : term_scope.

Notation "'let' 'fix' f x1 x2 .. xn := t1 'in' t2" :=
  (TLet (TFix (T2 f x1 (TFun (T1 x2 .. (TFun (T1 xn t1)) ..)))) (T1 f t2))
    (in custom term at level 69,
        f, x1, x2, xn at level 0,
        t1 custom term,
        t2 custom term,
        right associativity) : term_scope.

Notation "'shift' k t" :=
  (TShift (T1 k t))
    (in custom term at level 69,
        k at level 0,
        t custom term at level 99) : term_scope.

Notation "'control' k t" :=
  (TControl (T1 k t))
    (in custom term at level 69,
        k at level 0,
        t custom term at level 99) : term_scope.

Notation "'reset' t" :=
  (TReset t) (in custom term at level 69, t custom term) : term_scope.

Notation "'prompt' t" :=
  (TPrompt t) (in custom term at level 69, t custom term) : term_scope.

Notation "'fun' x1 .. xn => t" :=
  (TFun (T1 x1 .. (TFun (T1 xn t)) ..))
    (in custom term at level 69,
        x1, xn at level 0,
        t custom term at level 99) : term_scope.

Notation "'fix' f x := t" :=
  (TFix (T2 f x t))
    (in custom term at level 69,
        f, x at level 0,
        t custom term at level 99) : term_scope.

Notation "'fix' f x1 x2 .. xn := t" :=
  (TFix (T2 f x1 (TFun (T1 x2 .. (TFun (T1 xn t)) ..))))
    (in custom term at level 69,
        f, x1, x2, xn at level 0,
        t custom term at level 99) : term_scope.

Notation "()" := AUnit (in custom term at level 0) : term_scope.
Notation "'_'" := BAnon (in custom term at level 0) : term_scope.

Notation "'not' a" :=
  (TPrim1 P1Not a) (in custom term at level 23, a custom term at level 0) : term_scope.

Notation "'ref' a" :=
  (TRef a) (in custom term at level 23, a custom term at level 0) : term_scope.

Notation "! a" :=
  (TGet a) (in custom term at level 23, a custom term at level 0) : term_scope.

Notation "'free' a" :=
  (TFree a) (in custom term at level 23, a custom term at level 0) : term_scope.

Notation "a1 + a2" :=
  (TPrim2 P2Add a1 a2)
    (in custom term at level 40,
        a1 custom term,
        a2 custom term) : term_scope.

Notation "a1 - a2" :=
  (TPrim2 P2Sub a1 a2)
    (in custom term at level 40,
        a1 custom term,
        a2 custom term) : term_scope.

Notation "a1 * a2" :=
  (TPrim2 P2Mul a1 a2)
    (in custom term at level 39,
        a1 custom term,
        a2 custom term) : term_scope.

Notation "a1 = a2" :=
  (TPrim2 P2Eq a1 a2)
    (in custom term at level 50,
        a1 custom term,
        a2 custom term) : term_scope.

Notation "a1 <> a2" :=
  (TPrim2 P2Eq a1 a2)
    (in custom term at level 50,
        a1 custom term,
        a2 custom term) : term_scope.

Notation "a1 < a2" :=
  (TPrim2 P2Lt a1 a2)
    (in custom term at level 50,
        a1 custom term,
        a2 custom term) : term_scope.

Notation "a1 <= a2" :=
  (TPrim2 P2Le a1 a2)
    (in custom term at level 50,
        a1 custom term,
        a2 custom term) : term_scope.

Notation "a1 > a2" :=
  (TPrim2 P2Gt a1 a2)
    (in custom term at level 50,
        a1 custom term,
        a2 custom term) : term_scope.

Notation "a1 >= a2" :=
  (TPrim2 P2Ge a1 a2)
    (in custom term at level 50,
        a1 custom term,
        a2 custom term) : term_scope.

Notation "a1 && a2" :=
  (TPrim2 P2And a1 a2)
    (in custom term at level 50,
        a1 custom term,
        a2 custom term) : term_scope.

Notation "a1 || a2" :=
  (TPrim2 P2Or a1 a2)
    (in custom term at level 50,
        a1 custom term,
        a2 custom term) : term_scope.

Notation "a1 'xor' a2" :=
  (TPrim2 P2And a1 a2)
    (in custom term at level 50,
        a1 custom term,
        a2 custom term) : term_scope.

Notation "a1 <- a2" :=
  (TSet a1 a2)
    (in custom term at level 65,
        a1 custom term,
        a2 custom term) : term_scope.

Notation "a1 , a2" :=
  (TPair a1 a2)
    (in custom term at level 65,
        a1 custom term,
        a2 custom term) : term_scope.

Notation "'let' ( x1 , x2 ) := a 'in' t" :=
  (TSplit a (T2 x1 x2 t))
    (in custom term at level 69,
        x1, x2 at level 0,
        t custom term,
        right associativity) : term_scope.

Notation "'let' x1 , x2 := a 'in' t" :=
  (TSplit a (T2 x1 x2 t))
    (in custom term at level 69,
        x1, x2 at level 0,
        t custom term,
        right associativity) : term_scope.

Notation "'Inl' a" :=
  (TInl a) (in custom term at level 23, a custom term at level 0) : term_scope.

Notation "'Inr' a" :=
  (TInr a) (in custom term at level 23, a custom term at level 0) : term_scope.

Notation "'match' a 'with' | 'Inl' x1 => t1 | 'Inr' x2 => t2 'end'" :=
  (TCase a (T1 x1 t1) (T1 x2 t2))
    (in custom term at level 69,
        a custom term,
        x1, x2 at level 0,
        t1 custom term,
        t2 custom term) : term_scope.
