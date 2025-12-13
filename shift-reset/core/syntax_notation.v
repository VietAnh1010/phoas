From shift_reset.core Require Import syntax.

Declare Scope term_scope.
Delimit Scope term_scope with term.
Bind Scope term_scope with term.
Local Open Scope term_scope.

Declare Custom Entry binder'.
Declare Custom Entry variant_pattern.
Declare Custom Entry record_pattern.
Declare Custom Entry term.
Declare Custom Entry ret_term.
Declare Custom Entry exn_term.
Declare Custom Entry eff_term.
Declare Custom Entry variant_term.
Declare Custom Entry record_term.
Declare Custom Entry fix_mut_term.

Notation "'_'" := BAny (in custom binder' at level 0) : term_scope.
Notation "x" := x (in custom binder' at level 0, x constr at level 0) : term_scope.

Notation "'_'" := PVariantAny (in custom variant_pattern at level 0) : term_scope.
Notation "x" := x (in custom variant_pattern at level 0, x constr at level 0) : term_scope.

Notation "' ( l x )" :=
  (PVariantTag l x)
    (in custom variant_pattern at level 0,
        l constr at level 0,
        x custom binder' at level 0) : term_scope.

Notation "` l x" :=
  (PVariantTag l x)
    (in custom variant_pattern at level 0,
        l constr at level 0,
        x custom binder' at level 0) : term_scope.

Notation "<{ t }>" := t (t custom term at level 99) : term_scope.
Notation "( t )" := t (in custom term, t at level 99) : term_scope.
Notation "{ t }" := t (in custom term, t constr) : term_scope.
Notation "t" := t (in custom term at level 0, t constr at level 0) : term_scope.

Notation "( 'fun' x => t )" :=
  (TRetSome x t) (in custom ret_term at level 69, x custom binder' at level 0, t custom term) : term_scope.

Notation "( 'fun' p => t )" :=
  (TExnLast p t) (in custom exn_term at level 69, p custom variant_pattern at level 0, t custom term) : term_scope.

Notation "( 'fun' p => t1 ) ; t2" :=
  (TExnCons p t1 t2)
    (in custom exn_term at level 69,
        p custom variant_pattern at level 0,
        t1 custom term,
        t2 custom exn_term,
        right associativity) : term_scope.

Notation "( 'fun' p , k => t )" :=
  (TEffLast p k t)
    (in custom eff_term at level 69,
        p custom variant_pattern at level 0,
        k custom binder' at level 0,
        t custom term) : term_scope.

Notation "( 'fun' p , k => t1 ) ; t2" :=
  (TEffCons p k t1 t2)
    (in custom eff_term at level 69,
        p custom variant_pattern at level 0,
        k custom binder' at level 0,
        t1 custom term,
        t2 custom eff_term,
        right associativity) : term_scope.

Notation "| p => t" :=
  (TVariantCons p t TVariantNil)
    (in custom variant_term at level 69,
        p custom variant_pattern at level 0,
        t custom term) : term_scope.

Notation "| p => t1 t2" :=
  (TVariantCons p t1 t2)
    (in custom variant_term at level 69,
        p custom variant_pattern at level 0,
        t1 custom term,
        t2 custom variant_term,
        right associativity) : term_scope.

Notation "t1 t2" :=
  (TApp t1 t2) (in custom term at level 17, t1 custom term, t2 custom term) : term_scope.

Notation "'if' tv 'then' t1 'else' t2" :=
  (TIf tv t1 t2)
    (in custom term at level 69,
        tv custom term,
        t1 custom term,
        t2 custom term) : term_scope.

Notation "'let' x := t1 'in' t2" :=
  (TLet x t1 t2)
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
  (TLet f (TVFun x1 .. (TVFun xn t1) ..) t2)
    (in custom term at level 69,
        f custom binder' at level 0,
        x1 custom binder' at level 0,
        xn custom binder' at level 0,
        t1 custom term,
        t2 custom term,
        right associativity) : term_scope.

Notation "'let' 'fix' f x := t1 'in' t2" :=
  (TLetFix f x t1 t2)
    (in custom term at level 69,
        f constr at level 0,
        x custom binder' at level 0,
        t1 custom term,
        t2 custom term,
        right associativity) : term_scope.

Notation "'let' 'fix' f x1 x2 .. xn := t1 'in' t2" :=
  (TLetFix f x1 (TVFun x2 .. (TVFun xn t1) ..) t2)
    (in custom term at level 69,
        f constr at level 0,
        x1 custom binder' at level 0,
        x2 custom binder' at level 0,
        xn custom binder' at level 0,
        t1 custom term,
        t2 custom term,
        right associativity) : term_scope.

Notation "'while' tv 'do' t" :=
  (TWhile tv t) (in custom term at level 69, tv custom term, t custom term) : term_scope.

Notation "'for' x 'from' tv1 'upto' tv2 'do' t" :=
  (TFor x tv1 Upto tv2 t)
    (in custom term at level 69,
        x custom binder' at level 0,
        tv1 custom term,
        tv2 custom term,
        t custom term) : term_scope.

Notation "'for' x 'from' tv1 'downto' tv2 'do' t" :=
  (TFor x tv1 Downto tv2 t)
    (in custom term at level 69,
        x custom binder' at level 0,
        tv1 custom term,
        tv2 custom term,
        t custom term) : term_scope.

Notation "'shift' ( 'fun' k => t )" :=
  (TShift k t) (in custom term at level 69, k custom binder' at level 0, t custom term) : term_scope.

Notation "'control' ( 'fun' k => t )" :=
  (TControl k t) (in custom term at level 69, k custom binder' at level 0, t custom term) : term_scope.

Notation "'reset' t" :=
  (TReset t) (in custom term at level 69, t custom term) : term_scope.

Notation "'prompt' t" :=
  (TPrompt t) (in custom term at level 69, t custom term) : term_scope.

Notation "'fun' x1 .. xn => t" :=
  (TVFun x1 .. (TVFun xn t) ..)
    (in custom term at level 69,
        x1 custom binder' at level 0,
        xn custom binder' at level 0,
        t custom term at level 99) : term_scope.

Notation "'fix' f x := t" :=
  (TVFix f x t)
    (in custom term at level 69,
        f constr at level 0,
        x custom binder' at level 0,
        t custom term at level 99) : term_scope.

Notation "'fix' f x1 x2 .. xn := t" :=
  (TVFix f x1 (TVFun x2 .. (TVFun xn t) ..))
    (in custom term at level 69,
        f constr at level 0,
        x1 custom binder' at level 0,
        x2 custom binder' at level 0,
        xn custom binder' at level 0,
        t custom term at level 99) : term_scope.

Notation "f x := t1 'with' t2" :=
  (TFixMutCons f x t1 t2)
    (in custom fix_mut_term at level 69,
        f constr at level 0,
        x custom binder' at level 0,
        t1 custom term,
        t2 custom fix_mut_term) : term_scope.

Notation "f x1 x2 .. xn := t1 'with' t2" :=
  (TFixMutCons f x1 (TVFun x2 .. (TVFun xn t1) ..) t2)
    (in custom fix_mut_term at level 69,
        f constr at level 0,
        x1 custom binder' at level 0,
        x2 custom binder' at level 0,
        xn custom binder' at level 0,
        t1 custom term,
        t2 custom fix_mut_term) : term_scope.

Notation "f x := t" :=
  (TFixMutLast f x t)
    (in custom fix_mut_term at level 69,
        f constr at level 0,
        x custom binder' at level 0,
        t custom term) : term_scope.

Notation "f x1 x2 .. xn := t" :=
  (TFixMutLast f x1 (TVFun x2 .. (TVFun xn t) ..))
    (in custom fix_mut_term at level 69,
        f constr at level 0,
        x1 custom binder' at level 0,
        x2 custom binder' at level 0,
        xn custom binder' at level 0,
        t custom term) : term_scope.

Notation "'let' 'fix' f x := t1 'with' t2 'in' t3" :=
  (TLetFixMut (TFixMutCons f x t1 t2) t3)
    (in custom term at level 69,
        f constr at level 0,
        x custom binder' at level 0,
        t1 custom term,
        t2 custom fix_mut_term,
        t3 custom term) : term_scope.

Notation "'let' 'fix' f x1 x2 .. xn := t1 'with' t2 'in' t3" :=
  (TLetFixMut (TFixMutCons f x1 (TVFun x2 .. (TVFun xn t1) ..) t2) t3)
    (in custom term at level 69,
        f constr at level 0,
        x1 custom binder' at level 0,
        x2 custom binder' at level 0,
        xn custom binder' at level 0,
        t1 custom term,
        t2 custom fix_mut_term,
        t3 custom term) : term_scope.

Notation "'fix' f x := t1 'with' t2 'for' g" :=
  (TVFixMut (TFixMutCons f x t1 t2) g)
    (in custom term at level 69,
        f constr at level 0,
        x custom binder' at level 0,
        t1 custom term at level 99,
        t2 custom fix_mut_term,
        g constr at level 0) : term_scope.

Notation "'fix' f x1 x2 .. xn := t1 'with' t2 'for' g" :=
  (TVFixMut (TFixMutCons f x1 (TVFun x2 .. (TVFun xn t1) ..) t2) g)
    (in custom term at level 69,
        f constr at level 0,
        x1 custom binder' at level 0,
        x2 custom binder' at level 0,
        xn custom binder' at level 0,
        t1 custom term at level 99,
        t2 custom fix_mut_term,
        g constr at level 0) : term_scope.

Notation "()" := TVTt (in custom term at level 0) : term_scope.
Notation "'true'" := TVTrue (in custom term at level 0) : term_scope.
Notation "'false'" := TVFalse (in custom term at level 0) : term_scope.

Notation "+ t" :=
  (Op1Pos t) (in custom term at level 23, t custom term at level 0) : term_scope.

Notation "- t" :=
  (Op1Neg t) (in custom term at level 23, t custom term at level 0) : term_scope.

Notation "'not' t" :=
  (Op1Not t) (in custom term at level 23, t custom term at level 0) : term_scope.

Notation "'fst' t" :=
  (TVFst t) (in custom term at level 23, t custom term at level 0) : term_scope.

Notation "'snd' t" :=
  (TVSnd t) (in custom term at level 23, t custom term at level 0) : term_scope.

Notation "'ref' t" :=
  (TVRef t) (in custom term at level 23, t custom term at level 0) : term_scope.

Notation "! t" :=
  (TVGet t) (in custom term at level 23, t custom term at level 0) : term_scope.

Notation "'assert' t" :=
  (TVAssert t) (in custom term at level 23, t custom term at level 0) : term_scope.

Notation "t1 + t2" :=
  (Op2Add t1 t2) (in custom term at level 40, t1 custom term, t2 custom term) : term_scope.

Notation "t1 - t2" :=
  (Op2Sub t1 t2) (in custom term at level 40, t1 custom term, t2 custom term) : term_scope.

Notation "t1 * t2" :=
  (Op2Mul t1 t2) (in custom term at level 39, t1 custom term, t2 custom term) : term_scope.

Notation "t1 / t2" :=
  (Op2Div t1 t2) (in custom term at level 39, t1 custom term, t2 custom term) : term_scope.

Notation "t1 'mod' t2" :=
  (Op2Mod t1 t2) (in custom term at level 39, t1 custom term, t2 custom term) : term_scope.

Notation "t1 = t2" :=
  (Op2Eq t1 t2) (in custom term at level 50, t1 custom term, t2 custom term) : term_scope.

Notation "t1 < t2" :=
  (Op2Lt t1 t2) (in custom term at level 50, t1 custom term, t2 custom term) : term_scope.

Notation "t1 <= t2" :=
  (Op2Le t1 t2) (in custom term at level 50, t1 custom term, t2 custom term) : term_scope.

Notation "t1 > t2" :=
  (Op2Gt t1 t2) (in custom term at level 50, t1 custom term, t2 custom term) : term_scope.

Notation "t1 >= t2" :=
  (Op2Ge t1 t2) (in custom term at level 50, t1 custom term, t2 custom term) : term_scope.

Notation "t1 <> t2" :=
  (Op2Neq t1 t2) (in custom term at level 50, t1 custom term, t2 custom term) : term_scope.

Notation "t1 ++ t2" :=
  (Op2App t1 t2) (in custom term at level 49, t1 custom term, t2 custom term, right associativity) : term_scope.

Notation "t1 && t2" :=
  (TVAnd t1 t2) (in custom term at level 50, t1 custom term, t2 custom term, right associativity) : term_scope.

Notation "t1 || t2" :=
  (TVOr t1 t2) (in custom term at level 50, t1 custom term, t2 custom term, right associativity) : term_scope.

Notation "t1 <- t2" :=
  (TVSet t1 t2) (in custom term at level 65, t1 custom term, t2 custom term) : term_scope.

Notation "t1 , t2" :=
  (TVPair t1 t2) (in custom term at level 65, t1 custom term, t2 custom term) : term_scope.

Notation "`( t1 , t2 , t3 , .. , tn )" :=
  (TVTuple (TTupleCons t1 (TTupleCons t2 (TTupleCons t3 .. (TTupleCons tn TTupleNil) ..))))
    (in custom term at level 0,
        t1 custom term at level 23,
        t2 custom term at level 23,
        t3 custom term at level 23,
        tn custom term at level 23) : term_scope.

Notation "'let' ( x1 , x2 ) := tv 'in' t" :=
  (TSplit x1 x2 tv t)
    (in custom term at level 69,
        x1 custom binder' at level 0,
        x2 custom binder' at level 0,
        tv custom term,
        t custom term,
        right associativity) : term_scope.

Notation "'let' `( x1 , x2 , x3 , .. , xn ) := tv 'in' t" :=
  (TLetTuple (PTupleCons x1 (PTupleCons x2 (PTupleCons x3 .. (PTupleCons xn PTupleNil) ..))) tv t)
    (in custom term at level 69,
        x1 custom binder' at level 0,
        x2 custom binder' at level 0,
        x3 custom binder' at level 0,
        xn custom binder' at level 0,
        tv custom term,
        t custom term,
        right associativity) : term_scope.

Notation "'Inl' t" :=
  (TVInl t) (in custom term at level 23, t custom term at level 0) : term_scope.

Notation "'Inr' t" :=
  (TVInr t) (in custom term at level 23, t custom term at level 0) : term_scope.

Notation "'match' tv 'with' | 'Inl' x1 => t1 | 'Inr' x2 => t2 'end'" :=
  (TCase tv x1 t1 x2 t2)
    (in custom term at level 69,
        tv custom term,
        x1 custom binder' at level 0,
        x2 custom binder' at level 0,
        t1 custom term,
        t2 custom term) : term_scope.

Notation "'exception' l t" :=
  (TVExn l t)
    (in custom term at level 23,
        l constr at level 0,
        t custom term at level 0) : term_scope.

Notation "'raise' t" :=
  (TRaise t) (in custom term at level 23, t custom term at level 0) : term_scope.

Notation "'try' t1 ;; t2" :=
  (TTry t1 t2) (in custom term at level 69, t1 custom term, t2 custom exn_term) : term_scope.

Notation "'effect' l t" :=
  (TVEff l t)
    (in custom term at level 23,
        l constr at level 0,
        t custom term at level 0) : term_scope.

Notation "'perform' t" :=
  (TPerform t) (in custom term at level 23, t custom term at level 0) : term_scope.

Notation "'handle' t1 ;; t2 ;; t3" :=
  (THandle t1 t2 t3)
    (in custom term at level 69,
        t1 custom term,
        t2 custom ret_term,
        t3 custom eff_term) : term_scope.

Notation "'handle' t1 ;;; t2" :=
  (THandle t1 TRetNone t2)
    (in custom term at level 69,
        t1 custom term,
        t2 custom eff_term) : term_scope.

Notation "'shallow' 'handle' t1 ;; t2 ;; t3" :=
  (TShallowHandle t1 t2 t3)
    (in custom term at level 69,
        t1 custom term,
        t2 custom ret_term,
        t3 custom eff_term) : term_scope.

Notation "'shallow' 'handle' t1 ;;; t2" :=
  (TShallowHandle t1 TRetNone t2)
    (in custom term at level 69,
        t1 custom term,
        t2 custom eff_term) : term_scope.

Notation "` l t" :=
  (TVVariant l t)
    (in custom term at level 23,
        l constr at level 0,
        t custom term at level 0) : term_scope.

Notation "'match' tv 'with' t 'end'" :=
  (TMatchVariant tv t) (in custom term at level 69, tv custom term, t custom variant_term) : term_scope.

Notation "`{ l := t1 t2" :=
  (TVRecord (TRecordCons l t1 t2))
    (in custom term at level 0,
        l constr at level 0,
        t1 custom term at level 23,
        t2 custom record_term at level 23) : term_scope.

Notation "; l := t1 t2" :=
  (TRecordCons l t1 t2)
    (in custom record_term at level 23,
        l constr at level 0,
        t1 custom term at level 23,
        t2 custom record_term at level 23) : term_scope.

Notation "}" := TRecordNil (in custom record_term at level 23) : term_scope.

Notation "t .` l" :=
  (TVProj t l) (in custom term at level 23, l constr at level 0) : term_scope.

Notation "t1 .[ t2 ]" :=
  (TVGetAt t1 t2) (in custom term at level 64, t1 custom term, t2 custom term) : term_scope.

Notation "t1 .[ t2 ] <- t3" :=
  (TVSetAt t1 t2 t3)
    (in custom term at level 64,
        t1 custom term,
        t2 custom term,
        t3 custom term) : term_scope.

Notation "`[| t1 ; .. ; tn |]" :=
  (TVArray (TTupleCons t1 .. (TTupleCons tn TTupleNil) ..))
    (in custom term at level 0,
        t1 custom term at level 23,
        tn custom term at level 23) : term_scope.
