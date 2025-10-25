From shift_reset.core Require Import syntax tag.

Declare Scope term_scope.
Delimit Scope term_scope with term.
Bind Scope term_scope with term.
Local Open Scope term_scope.

Declare Custom Entry binder'.
Declare Custom Entry pattern'.
Declare Custom Entry term.
Declare Custom Entry term1.
Declare Custom Entry ret_term.
Declare Custom Entry exn_term.
Declare Custom Entry eff_term.

Notation "'_'" := BAny (in custom binder' at level 0) : term_scope.
Notation "x" := x (in custom binder' at level 0, x constr at level 0) : term_scope.

Notation "'_'" := PAny (in custom pattern' at level 0) : term_scope.
Notation "x" := x (in custom pattern' at level 0, x constr at level 0) : term_scope.

Notation "' ( tag x )" :=
  (PConstr tag x) (in custom pattern' at level 10, tag at level 0, x custom binder') : term_scope.

Notation "' ( tag x 'as' y )" :=
  (PAlias (PConstr tag x) y)
    (in custom pattern' at level 10,
        tag at level 0,
        x custom binder',
        y constr at level 0) : term_scope.

Notation "<{ t }>" := t (t custom term at level 99) : term_scope.
Notation "( t )" := t (in custom term, t at level 99) : term_scope.
Notation "{ t }" := t (in custom term, t constr) : term_scope.
Notation "t" := t (in custom term at level 0, t constr at level 0) : term_scope.

Notation "( 'fun' x => t )" :=
  (T1 x t)
    (in custom term1 at level 69,
        x custom binder' at level 0,
        t custom term) : term_scope.

Notation "( 'fun' x => t )" :=
  (TRetSome x t)
    (in custom ret_term at level 69,
        x custom binder' at level 0,
        t custom term) : term_scope.

Notation "( 'fun' x => t )" :=
  (TExnLast x t)
    (in custom exn_term at level 69,
        x custom pattern' at level 10,
        t custom term) : term_scope.

Notation "( 'fun' x => t1 ) ; t2" :=
  (TExnCons x t1 t2)
    (in custom exn_term at level 69,
        x custom pattern' at level 10,
        t1 custom term,
        t2 custom exn_term,
        right associativity) : term_scope.

Notation "( 'fun' x , k => t )" :=
  (TEffLast x k t)
    (in custom eff_term at level 69,
        x custom pattern' at level 10,
        k custom binder' at level 0,
        t custom term) : term_scope.

Notation "( 'fun' x , k => t1 ) ; t2" :=
  (TEffCons x k t1 t2)
    (in custom eff_term at level 69,
        x custom pattern' at level 10,
        k custom binder' at level 0,
        t1 custom term,
        t2 custom eff_term,
        right associativity) : term_scope.

Notation "t1 t2" :=
  (TApp t1 t2) (in custom term at level 10, t1 custom term, t2 custom term) : term_scope.

Notation "'if' t1 'then' t2 'else' t3" :=
  (TIf t1 t2 t3)
    (in custom term at level 69,
        t1 custom term,
        t2 custom term,
        t3 custom term) : term_scope.

Notation "'let' x := t1 'in' t2" :=
  (TLet t1 (T1 x t2))
    (in custom term at level 69,
        x custom binder' at level 0,
        t1 custom term,
        t2 custom term,
        right associativity) : term_scope.

Notation "t1 ; t2" :=
  (TSeq t1 t2)
    (in custom term at level 69,
        t1 custom term,
        t2 custom term,
        right associativity) : term_scope.

Notation "'let' f x1 .. xn := t1 'in' t2" :=
  (TLet (TVFun (T1 x1 .. (TVFun (T1 xn t1)) ..)) (T1 f t2))
    (in custom term at level 69,
        f custom binder' at level 0,
        x1 custom binder' at level 0,
        xn custom binder' at level 0,
        t1 custom term,
        t2 custom term,
        right associativity) : term_scope.

Notation "'let' 'fix' f x := t1 'in' t2" :=
  (TLet (TVFix (T2 f x t1)) (T1 f t2))
    (in custom term at level 69,
        f custom binder' at level 0,
        x custom binder' at level 0,
        t1 custom term,
        t2 custom term,
        right associativity) : term_scope.

Notation "'let' 'fix' f x1 x2 .. xn := t1 'in' t2" :=
  (TLet (TVFix (T2 f x1 (TVFun (T1 x2 .. (TVFun (T1 xn t1)) ..)))) (T1 f t2))
    (in custom term at level 69,
        f custom binder' at level 0,
        x1 custom binder' at level 0,
        x2 custom binder' at level 0,
        xn custom binder' at level 0,
        t1 custom term,
        t2 custom term,
        right associativity) : term_scope.

Notation "'shift' t" :=
  (TShift tag_empty t) (in custom term at level 69, t custom term1) : term_scope.

Notation "'shift' 'at' tag t" :=
  (TShift tag t) (in custom term at level 69, tag at level 0, t custom term1) : term_scope.

Notation "'control' t" :=
  (TControl tag_empty t) (in custom term at level 69, t custom term1) : term_scope.

Notation "'control' 'at' tag t" :=
  (TControl tag t) (in custom term at level 69, tag at level 0, t custom term1) : term_scope.

Notation "'reset' t" :=
  (TReset tag_empty t) (in custom term at level 69, t custom term) : term_scope.

Notation "'reset' 'at' tag t" :=
  (TReset tag t) (in custom term at level 69, tag at level 0, t custom term) : term_scope.

Notation "'prompt' t" :=
  (TPrompt tag_empty t) (in custom term at level 69, t custom term) : term_scope.

Notation "'prompt' 'at' tag t" :=
  (TPrompt tag t) (in custom term at level 69, tag at level 0, t custom term) : term_scope.

Notation "'fun' x1 .. xn => t" :=
  (TVFun (T1 x1 .. (TVFun (T1 xn t)) ..))
    (in custom term at level 69,
        x1 custom binder' at level 0,
        xn custom binder' at level 0,
        t custom term at level 99) : term_scope.

Notation "'fix' f x := t" :=
  (TVFix (T2 f x t))
    (in custom term at level 69,
        f custom binder' at level 0,
        x custom binder' at level 0,
        t custom term at level 99) : term_scope.

Notation "'fix' f x1 x2 .. xn := t" :=
  (TVFix (T2 f x1 (TVFun (T1 x2 .. (TVFun (T1 xn t)) ..))))
    (in custom term at level 69,
        f custom binder' at level 0,
        x1 custom binder' at level 0,
        x2 custom binder' at level 0,
        xn custom binder' at level 0,
        t custom term at level 99) : term_scope.

Notation "()" := TVUnit (in custom term at level 0) : term_scope.
Notation "'true'" := TVTrue (in custom term at level 0) : term_scope.
Notation "'false'" := TVFalse (in custom term at level 0) : term_scope.

Notation "'not' t" :=
  (TVNot t) (in custom term at level 23, t custom term at level 0) : term_scope.

Notation "- t" :=
  (TVNeg t) (in custom term at level 23, t custom term at level 0) : term_scope.

Notation "'ref' t" :=
  (TVRef t) (in custom term at level 23, t custom term at level 0) : term_scope.

Notation "! t" :=
  (TVGet t) (in custom term at level 23, t custom term at level 0) : term_scope.

Notation "'free' t" :=
  (TVFree t) (in custom term at level 23, t custom term at level 0) : term_scope.

Notation "'assert' t" :=
  (TVAssert t) (in custom term at level 23, t custom term at level 0) : term_scope.

Notation "t1 + t2" :=
  (TVAdd t1 t2) (in custom term at level 40, t1 custom term, t2 custom term) : term_scope.

Notation "t1 - t2" :=
  (TVSub t1 t2) (in custom term at level 40, t1 custom term, t2 custom term) : term_scope.

Notation "t1 * t2" :=
  (TVMul t1 t2) (in custom term at level 39, t1 custom term, t2 custom term) : term_scope.

Notation "t1 / t2" :=
  (TVDiv t1 t2) (in custom term at level 39, t1 custom term, t2 custom term) : term_scope.

Notation "t1 'mod' t2" :=
  (TVMod t1 t2) (in custom term at level 39, t1 custom term, t2 custom term) : term_scope.

Notation "t1 = t2" :=
  (TVEq t1 t2) (in custom term at level 50, t1 custom term, t2 custom term) : term_scope.

Notation "t1 <= t2" :=
  (TVLe t1 t2) (in custom term at level 50, t1 custom term, t2 custom term) : term_scope.

Notation "t1 > t2" :=
  (TVGt t1 t2) (in custom term at level 50, t1 custom term, t2 custom term) : term_scope.

Notation "t1 >= t2" :=
  (TVGe t1 t2) (in custom term at level 50, t1 custom term, t2 custom term) : term_scope.

Notation "t1 <> t2" :=
  (TVNeq t1 t2) (in custom term at level 50, t1 custom term, t2 custom term) : term_scope.

Notation "t1 < t2" :=
  (TVLt t1 t2) (in custom term at level 50, t1 custom term, t2 custom term) : term_scope.

Notation "t1 && t2" :=
  (TVAnd t1 t2) (in custom term at level 50, t1 custom term, t2 custom term, right associativity) : term_scope.

Notation "t1 || t2" :=
  (TVOr t1 t2) (in custom term at level 50, t1 custom term, t2 custom term, right associativity) : term_scope.

Notation "t1 <- t2" :=
  (TVSet t1 t2) (in custom term at level 65, t1 custom term, t2 custom term) : term_scope.

Notation "t1 , t2" :=
  (TVPair t1 t2) (in custom term at level 65, t1 custom term, t2 custom term) : term_scope.

Notation "'let' ( x1 , x2 ) := t1 'in' t2" :=
  (TSplit t1 (T2 x1 x2 t2))
    (in custom term at level 69,
        x1 custom binder' at level 0,
        x2 custom binder' at level 0,
        t1 custom term,
        t2 custom term,
        right associativity) : term_scope.

Notation "'let' x1 , x2 := t1 'in' t2" :=
  (TSplit t1 (T2 x1 x2 t2))
    (in custom term at level 69,
        x1 custom binder' at level 0,
        x2 custom binder' at level 0,
        t1 custom term,
        t2 custom term,
        right associativity) : term_scope.

Notation "'Inl' t" :=
  (TVInl t) (in custom term at level 23, t custom term at level 0) : term_scope.

Notation "'Inr' t" :=
  (TVInr t) (in custom term at level 23, t custom term at level 0) : term_scope.

Notation "'match' t0 'with' | 'Inl' x1 => t1 | 'Inr' x2 => t2 'end'" :=
  (TCase t0 (T1 x1 t1) (T1 x2 t2))
    (in custom term at level 69,
        t0 custom term,
        x1 custom binder' at level 0,
        x2 custom binder' at level 0,
        t1 custom term,
        t2 custom term) : term_scope.

Notation "'exception' tag t" :=
  (TVExn tag t)
    (in custom term at level 23,
        tag at level 0,
        t custom term at level 0) : term_scope.

Notation "'raise' t" :=
  (TRaise t) (in custom term at level 23, t custom term at level 0) : term_scope.

Notation "'try' t1 ;; t2" :=
  (TTry t1 t2)
    (in custom term at level 69,
        t1 custom term,
        t2 custom exn_term) : term_scope.

Notation "'effect' tag t" :=
  (TVEff tag t)
    (in custom term at level 23,
        tag at level 0,
        t custom term at level 0) : term_scope.

Notation "'perform' t" :=
  (TPerform t) (in custom term at level 23, t custom term at level 0) : term_scope.

Notation "'handle' t1 ;; t2 ;; t3" :=
  (THandle t1 t2 t3)
    (in custom term at level 23,
        t1 custom term,
        t2 custom ret_term,
        t3 custom eff_term) : term_scope.

Notation "'handle' t1 ;;; t2" :=
  (THandle t1 TRetNone t2)
    (in custom term at level 23,
        t1 custom term,
        t2 custom eff_term) : term_scope.

Notation "'shallow' 'handle' t1 ;; t2 ;; t3" :=
  (TShallowHandle t1 t2 t3)
    (in custom term at level 23,
        t1 custom term,
        t2 custom ret_term,
        t3 custom eff_term) : term_scope.

Notation "'shallow' 'handle' t1 ;;; t2" :=
  (TShallowHandle t1 TRetNone t2)
    (in custom term at level 23,
        t1 custom term,
        t2 custom eff_term) : term_scope.
