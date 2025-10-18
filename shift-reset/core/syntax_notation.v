From shift_reset.core Require Import syntax.

Declare Scope term_scope.
Delimit Scope term_scope with term.
Bind Scope term_scope with term.

Declare Custom Entry binder'.
Declare Custom Entry pattern'.
Declare Custom Entry term.
Declare Custom Entry term1.
Declare Custom Entry exn_term.

Notation "'_'" := BAny (in custom binder' at level 0) : term_scope.
Notation "x" := x (in custom binder' at level 0, x constr at level 0) : term_scope.

Notation "'_'" := PAny (in custom pattern' at level 0) : term_scope.
Notation "x" := x (in custom pattern' at level 0, x constr at level 0) : term_scope.

Notation "' ( tag x )" :=
  (PTag tag x) (in custom pattern' at level 10, tag at level 0, x custom binder') : term_scope.

Notation "<{ t }>" := t (t custom term at level 99) : term_scope.
Notation "( t )" := t (in custom term, t at level 99) : term_scope.
Notation "{ t }" := t (in custom term, t constr) : term_scope.
Notation "t" := t (in custom term at level 0, t constr at level 0) : term_scope.

Notation "( t )" := t (in custom term1, t at level 99) : term_scope.
Notation "( t )" := t (in custom exn_term, t at level 99) : term_scope.

Notation "'fun' x => t" :=
  (T1 x t)
    (in custom term1 at level 69,
        x custom binder' at level 0,
        t custom term) : term_scope.

Notation "'fun' x => t" :=
  (ExnTBase x t)
    (in custom exn_term at level 69,
        x custom pattern' at level 10,
        t custom term) : term_scope.

Notation "'fun' x => t1 ; t2" :=
  (ExnTCons x t1 t2)
    (in custom exn_term at level 69,
        x custom pattern' at level 10,
        t1 custom term,
        t2 custom exn_term,
        right associativity) : term_scope.

Notation "a1 a2" :=
  (TApp a1 a2) (in custom term at level 10, a1 custom term, a2 custom term) : term_scope.

Notation "'if' a 'then' t1 'else' t2" :=
  (TIf a t1 t2)
    (in custom term at level 69,
        a custom term,
        t1 custom term,
        t2 custom term) : term_scope.

Notation "'let' x := t1 'in' t2" :=
  (TLet t1 (T1 x t2))
    (in custom term at level 69,
        x custom binder' at level 0,
        t1 custom term,
        t2 custom term,
        right associativity) : term_scope.

Notation "'let' f x1 .. xn := t1 'in' t2" :=
  (TLet (TFun (T1 x1 .. (TFun (T1 xn t1)) ..)) (T1 f t2))
    (in custom term at level 69,
        f custom binder' at level 0,
        x1 custom binder' at level 0,
        xn custom binder' at level 0,
        t1 custom term,
        t2 custom term,
        right associativity) : term_scope.

Notation "'let' 'fix' f x := t1 'in' t2" :=
  (TLet (TFix (T2 f x t1)) (T1 f t2))
    (in custom term at level 69,
        f custom binder' at level 0,
        x custom binder' at level 0,
        t1 custom term,
        t2 custom term,
        right associativity) : term_scope.

Notation "'let' 'fix' f x1 x2 .. xn := t1 'in' t2" :=
  (TLet (TFix (T2 f x1 (TFun (T1 x2 .. (TFun (T1 xn t1)) ..)))) (T1 f t2))
    (in custom term at level 69,
        f custom binder' at level 0,
        x1 custom binder' at level 0,
        x2 custom binder' at level 0,
        xn custom binder' at level 0,
        t1 custom term,
        t2 custom term,
        right associativity) : term_scope.

Notation "'shift' t" :=
  (TShift t) (in custom term at level 69, t custom term1) : term_scope.

Notation "'control' t" :=
  (TControl t) (in custom term at level 69, t custom term1) : term_scope.

Notation "'reset' t" :=
  (TReset t) (in custom term at level 69, t custom term) : term_scope.

Notation "'prompt' t" :=
  (TPrompt t) (in custom term at level 69, t custom term) : term_scope.

Notation "'fun' x1 .. xn => t" :=
  (TFun (T1 x1 .. (TFun (T1 xn t)) ..))
    (in custom term at level 69,
        x1 custom binder' at level 0,
        xn custom binder' at level 0,
        t custom term at level 99) : term_scope.

Notation "'fix' f x := t" :=
  (TFix (T2 f x t))
    (in custom term at level 69,
        f custom binder' at level 0,
        x custom binder' at level 0,
        t custom term at level 99) : term_scope.

Notation "'fix' f x1 x2 .. xn := t" :=
  (TFix (T2 f x1 (TFun (T1 x2 .. (TFun (T1 xn t)) ..))))
    (in custom term at level 69,
        f custom binder' at level 0,
        x1 custom binder' at level 0,
        x2 custom binder' at level 0,
        xn custom binder' at level 0,
        t custom term at level 99) : term_scope.

Notation "()" := AUnit (in custom term at level 0) : term_scope.

Notation "'not' a" :=
  (TPrim1 P1Not a) (in custom term at level 23, a custom term at level 0) : term_scope.

Notation "- a" :=
  (TPrim1 P1Neg a) (in custom term at level 23, a custom term at level 0) : term_scope.

Notation "'ref' a" :=
  (TRef a) (in custom term at level 23, a custom term at level 0) : term_scope.

Notation "! a" :=
  (TGet a) (in custom term at level 23, a custom term at level 0) : term_scope.

Notation "'free' a" :=
  (TFree a) (in custom term at level 23, a custom term at level 0) : term_scope.

Notation "a1 + a2" :=
  (TPrim2 P2Add a1 a2) (in custom term at level 40, a1 custom term, a2 custom term) : term_scope.

Notation "a1 - a2" :=
  (TPrim2 P2Sub a1 a2) (in custom term at level 40, a1 custom term, a2 custom term) : term_scope.

Notation "a1 * a2" :=
  (TPrim2 P2Mul a1 a2) (in custom term at level 39, a1 custom term, a2 custom term) : term_scope.

Notation "a1 = a2" :=
  (TPrim2 P2Eq a1 a2) (in custom term at level 50, a1 custom term, a2 custom term) : term_scope.

Notation "a1 <> a2" :=
  (TPrim2 P2Neq a1 a2) (in custom term at level 50, a1 custom term, a2 custom term) : term_scope.

Notation "a1 < a2" :=
  (TPrim2 P2Lt a1 a2) (in custom term at level 50, a1 custom term, a2 custom term) : term_scope.

Notation "a1 <= a2" :=
  (TPrim2 P2Le a1 a2) (in custom term at level 50, a1 custom term, a2 custom term) : term_scope.

Notation "a1 > a2" :=
  (TPrim2 P2Gt a1 a2) (in custom term at level 50, a1 custom term, a2 custom term) : term_scope.

Notation "a1 >= a2" :=
  (TPrim2 P2Ge a1 a2) (in custom term at level 50, a1 custom term, a2 custom term) : term_scope.

Notation "a1 && a2" :=
  (TPrim2 P2And a1 a2) (in custom term at level 50, a1 custom term, a2 custom term) : term_scope.

Notation "a1 || a2" :=
  (TPrim2 P2Or a1 a2) (in custom term at level 50, a1 custom term, a2 custom term) : term_scope.

Notation "a1 'xor' a2" :=
  (TPrim2 P2Xor a1 a2) (in custom term at level 50, a1 custom term, a2 custom term) : term_scope.

Notation "a1 <- a2" :=
  (TSet a1 a2) (in custom term at level 65, a1 custom term, a2 custom term) : term_scope.

Notation "a1 , a2" :=
  (TPair a1 a2) (in custom term at level 65, a1 custom term, a2 custom term) : term_scope.

Notation "'let' ( x1 , x2 ) := a 'in' t" :=
  (TSplit a (T2 x1 x2 t))
    (in custom term at level 69,
        x1 custom binder' at level 0,
        x2 custom binder' at level 0,
        a custom term,
        t custom term,
        right associativity) : term_scope.

Notation "'let' x1 , x2 := a 'in' t" :=
  (TSplit a (T2 x1 x2 t))
    (in custom term at level 69,
        x1 custom binder' at level 0,
        x2 custom binder' at level 0,
        a custom term,
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
        x1 custom binder' at level 0,
        x2 custom binder' at level 0,
        t1 custom term,
        t2 custom term) : term_scope.

Notation "'exception' tag a" :=
  (TExn tag a)
    (in custom term at level 23,
        tag at level 0,
        a custom term at level 0) : term_scope.

Notation "'raise' a" :=
  (TRaise a) (in custom term at level 23, a custom term at level 0) : term_scope.

Notation "'try' t1 ; t2" :=
  (TTry t1 t2)
    (in custom term at level 69,
        t1 custom term,
        t2 custom exn_term) : term_scope.
