From shift_reset.core Require Import syntax.

Declare Scope term_scope.
Delimit Scope term_scope with term.
Bind Scope term_scope with term.
Local Open Scope term_scope.

Declare Custom Entry binder'.
Declare Custom Entry pattern'.
Declare Custom Entry tuple_pattern.
Declare Custom Entry record_pattern.
Declare Custom Entry term.
Declare Custom Entry match_term.
Declare Custom Entry fix_mut_term.
Declare Custom Entry ret_term.
Declare Custom Entry exn_term.
Declare Custom Entry eff_term.
Declare Custom Entry tuple_term.
Declare Custom Entry record_term.

Notation "'_'" := BAny (in custom binder' at level 0) : term_scope.
Notation "b" := b (in custom binder' at level 0, b constr at level 0) : term_scope.

Notation "( p )" := p (in custom pattern', p at level 99) : term_scope.
Notation "{ p }" := p (in custom pattern', p constr) : term_scope.
Notation "p" := p (in custom pattern' at level 0, p constr at level 0) : term_scope.
Notation "'_'" := PAny (in custom pattern' at level 0) : term_scope.

Notation "p 'as' x" :=
  (PAlias p x) (in custom pattern' at level 67, p custom pattern', x constr at level 0) : term_scope.

Notation "p1 | p2" :=
  (POr p1 p2) (in custom pattern' at level 66, p1 custom pattern', p2 custom pattern', right associativity) : term_scope.

Notation "()" := PTt (in custom pattern' at level 0) : term_scope.
Notation "'true'" := PTrue (in custom pattern' at level 0) : term_scope.
Notation "'false'" := PFalse (in custom pattern' at level 0) : term_scope.

Notation "p1 , p2" :=
  (PPair p1 p2) (in custom pattern' at level 65, p1 custom pattern', p2 custom pattern', left associativity) : term_scope.

Notation "`( p )" :=
  (PTuple p) (in custom pattern' at level 0, p custom tuple_pattern at level 0) : term_scope.

Notation "`{ p }" :=
  (PRecord p) (in custom pattern' at level 0, p custom record_pattern at level 0) : term_scope.

Notation "'Inl' p" :=
  (PInl p) (in custom pattern' at level 23, p custom pattern' at level 10) : term_scope.

Notation "'Inr' p" :=
  (PInr p) (in custom pattern' at level 23, p custom pattern' at level 10) : term_scope.

Notation "` l p" :=
  (PVariant l p) (in custom pattern' at level 23, l constr at level 0, p custom pattern' at level 0) : term_scope.

Notation "p" :=
  (PTupleCons p PTupleNil) (in custom tuple_pattern at level 0, p custom pattern' at level 64) : term_scope.

Notation "p1 , p2" :=
  (PTupleCons p1 p2) (in custom tuple_pattern at level 0, p1 custom pattern' at level 64, p2 custom tuple_pattern at level 0) : term_scope.

Notation "'..' p" :=
  (PRecordRest p) (in custom record_pattern at level 0, p custom pattern' at level 65) : term_scope.

Notation "l" :=
  (PRecordCons0 l PRecordNil) (in custom record_pattern at level 0, l constr at level 0) : term_scope.

Notation "l ; p" :=
  (PRecordCons0 l p) (in custom record_pattern at level 0, l constr at level 0, p custom record_pattern at level 0) : term_scope.

Notation "l := p" :=
  (PRecordCons1 l p PRecordNil) (in custom record_pattern at level 0, l constr at level 0, p custom pattern' at level 65) : term_scope.

Notation "l := p1 ; p2" :=
  (PRecordCons1 l p1 p2) (in custom record_pattern at level 0,
        l constr at level 0,
        p1 custom pattern' at level 65,
        p2 custom record_pattern at level 0) : term_scope.

Notation "<{ t }>" := t (t custom term at level 99) : term_scope.
Notation "( t )" := t (in custom term, t at level 99) : term_scope.
Notation "{ t }" := t (in custom term, t constr) : term_scope.
Notation "t" := t (in custom term at level 0, t constr at level 0) : term_scope.

Notation "| p => t" :=
  (TMatchCons p t TMatchNil) (in custom match_term at level 69, p custom pattern' at level 69, t custom term) : term_scope.

Notation "| p => t1 t2" :=
  (TMatchCons p t1 t2) (in custom match_term at level 69,
        p custom pattern' at level 69,
        t1 custom term,
        t2 custom match_term,
        right associativity) : term_scope.

Notation "( 'fun' p => t )" :=
  (TRetSome p t) (in custom ret_term at level 69, p custom pattern' at level 0, t custom term) : term_scope.

Notation "( 'fun' p => t )" :=
  (TExnLast p t) (in custom exn_term at level 69, p custom pattern' at level 0, t custom term) : term_scope.

Notation "( 'fun' p => t1 ) ; t2" :=
  (TExnCons p t1 t2) (in custom exn_term at level 69,
        p custom pattern' at level 0,
        t1 custom term,
        t2 custom exn_term,
        right associativity) : term_scope.

Notation "( 'fun' p k => t )" :=
  (TEffLast p k t) (in custom eff_term at level 69,
        p custom pattern' at level 0,
        k custom binder' at level 0,
        t custom term) : term_scope.

Notation "( 'fun' p k => t1 ) ; t2" :=
  (TEffCons p k t1 t2) (in custom eff_term at level 69,
        p custom pattern' at level 0,
        k custom binder' at level 0,
        t1 custom term,
        t2 custom eff_term,
        right associativity) : term_scope.

Notation "t1 t2" :=
  (TApp t1 t2) (in custom term at level 17, t1 custom term, t2 custom term) : term_scope.

Notation "'if' tv 'then' t1 'else' t2" :=
  (TIf tv t1 t2) (in custom term at level 69,
        tv custom term,
        t1 custom term,
        t2 custom term) : term_scope.

Notation "t1 ; t2" :=
  (TSeq t1 t2) (in custom term at level 69, t1 custom term, t2 custom term, right associativity) : term_scope.

Notation "'let' p := t1 'in' t2" :=
  (TLet p t1 t2) (in custom term at level 69,
        p custom pattern' at level 0,
        t1 custom term,
        t2 custom term,
        right associativity) : term_scope.

Notation "'match' t1 'with' t2 'end'" :=
  (TMatch t1 t2) (in custom term at level 69, t1 custom term, t2 custom match_term) : term_scope.

Notation "'let' f p1 .. pn := t1 'in' t2" :=
  (TLet f (TVFun p1 .. (TVFun pn t1) ..) t2) (in custom term at level 69,
        f custom pattern' at level 0,
        p1 custom pattern' at level 0,
        pn custom pattern' at level 0,
        t1 custom term,
        t2 custom term,
        right associativity) : term_scope.

Notation "'let' 'fix' f p := t1 'in' t2" :=
  (TLetFix f p t1 t2) (in custom term at level 69,
        f constr at level 0,
        p custom pattern' at level 0,
        t1 custom term,
        t2 custom term,
        right associativity) : term_scope.

Notation "'let' 'fix' f p1 p2 .. pn := t1 'in' t2" :=
  (TLetFix f p1 (TVFun p2 .. (TVFun pn t1) ..) t2) (in custom term at level 69,
        f constr at level 0,
        p1 custom pattern' at level 0,
        p2 custom pattern' at level 0,
        pn custom pattern' at level 0,
        t1 custom term,
        t2 custom term,
        right associativity) : term_scope.

Notation "'while' tv 'do' t" :=
  (TWhile tv t) (in custom term at level 69, tv custom term, t custom term) : term_scope.

Notation "'for' b 'from' tv1 'upto' tv2 'do' t" :=
  (TFor b tv1 Upto tv2 t) (in custom term at level 69,
        b custom binder' at level 0,
        tv1 custom term,
        tv2 custom term,
        t custom term) : term_scope.

Notation "'for' b 'from' tv1 'downto' tv2 'do' t" :=
  (TFor b tv1 Downto tv2 t) (in custom term at level 69,
        b custom binder' at level 0,
        tv1 custom term,
        tv2 custom term,
        t custom term) : term_scope.

Notation "'shift' ( 'fun' k => t )" :=
  (TShift k t) (in custom term at level 69, k custom binder' at level 0, t custom term) : term_scope.

Notation "'control' ( 'fun' k => t )" :=
  (TControl k t) (in custom term at level 69, k custom binder' at level 0, t custom term) : term_scope.

Notation "'shift0' ( 'fun' k => t )" :=
  (TShift0 k t) (in custom term at level 69, k custom binder' at level 0, t custom term) : term_scope.

Notation "'control0' ( 'fun' k => t )" :=
  (TControl0 k t) (in custom term at level 69, k custom binder' at level 0, t custom term) : term_scope.

Notation "'reset' t" :=
  (TReset t) (in custom term at level 69, t custom term) : term_scope.

Notation "'prompt' t" :=
  (TPrompt t) (in custom term at level 69, t custom term) : term_scope.

Notation "'reset0' t" :=
  (TReset0 t) (in custom term at level 69, t custom term) : term_scope.

Notation "'prompt0' t" :=
  (TPrompt0 t) (in custom term at level 69, t custom term) : term_scope.

Notation "'fun' p1 .. pn => t" :=
  (TVFun p1 .. (TVFun pn t) ..) (in custom term at level 60,
        p1 custom pattern' at level 0,
        pn custom pattern' at level 0,
        t custom term at level 99) : term_scope.

Notation "'fix' f p := t" :=
  (TVFix f p t) (in custom term at level 60,
        f constr at level 0,
        p custom pattern' at level 0,
        t custom term at level 99) : term_scope.

Notation "'fix' f p1 p2 .. pn := t" :=
  (TVFix f p1 (TVFun p2 .. (TVFun pn t) ..)) (in custom term at level 60,
        f constr at level 0,
        p1 custom pattern' at level 0,
        p2 custom pattern' at level 0,
        pn custom pattern' at level 0,
        t custom term at level 99) : term_scope.

Notation "f p := t1 'with' t2" :=
  (TFixMutCons f p t1 t2) (in custom fix_mut_term at level 69,
        f constr at level 0,
        p custom pattern' at level 0,
        t1 custom term,
        t2 custom fix_mut_term) : term_scope.

Notation "f p1 p2 .. pn := t1 'with' t2" :=
  (TFixMutCons f p1 (TVFun p2 .. (TVFun pn t1) ..) t2) (in custom fix_mut_term at level 69,
        f constr at level 0,
        p1 custom pattern' at level 0,
        p2 custom pattern' at level 0,
        pn custom pattern' at level 0,
        t1 custom term,
        t2 custom fix_mut_term) : term_scope.

Notation "f p := t" :=
  (TFixMutLast f p t) (in custom fix_mut_term at level 69,
        f constr at level 0,
        p custom pattern' at level 0,
        t custom term) : term_scope.

Notation "f p1 p2 .. pn := t" :=
  (TFixMutLast f p1 (TVFun p2 .. (TVFun pn t) ..)) (in custom fix_mut_term at level 69,
        f constr at level 0,
        p1 custom pattern' at level 0,
        p2 custom pattern' at level 0,
        pn custom pattern' at level 0,
        t custom term) : term_scope.

Notation "'let' 'fix' f p := t1 'with' t2 'in' t3" :=
  (TLetFixMut (TFixMutCons f p t1 t2) t3) (in custom term at level 69,
        f constr at level 0,
        p custom pattern' at level 0,
        t1 custom term,
        t2 custom fix_mut_term,
        t3 custom term) : term_scope.

Notation "'let' 'fix' f p1 p2 .. pn := t1 'with' t2 'in' t3" :=
  (TLetFixMut (TFixMutCons f p1 (TVFun p2 .. (TVFun pn t1) ..) t2) t3) (in custom term at level 69,
        f constr at level 0,
        p1 custom pattern' at level 0,
        p2 custom pattern' at level 0,
        pn custom pattern' at level 0,
        t1 custom term,
        t2 custom fix_mut_term,
        t3 custom term) : term_scope.

Notation "'fix' f p := t1 'with' t2 'for' g" :=
  (TVFixMut (TFixMutCons f p t1 t2) g) (in custom term at level 60,
        f constr at level 0,
        p custom pattern' at level 0,
        t1 custom term at level 99,
        t2 custom fix_mut_term,
        g constr at level 0) : term_scope.

Notation "'fix' f p1 p2 .. pn := t1 'with' t2 'for' g" :=
  (TVFixMut (TFixMutCons f p1 (TVFun p2 .. (TVFun pn t1) ..) t2) g) (in custom term at level 60,
        f constr at level 0,
        p1 custom pattern' at level 0,
        p2 custom pattern' at level 0,
        pn custom pattern' at level 0,
        t1 custom term at level 99,
        t2 custom fix_mut_term,
        g constr at level 0) : term_scope.

Notation "()" := TVTt (in custom term at level 0) : term_scope.
Notation "'true'" := TVTrue (in custom term at level 0) : term_scope.
Notation "'false'" := TVFalse (in custom term at level 0) : term_scope.

Notation "! t" :=
  (TVGet t) (in custom term at level 1, t custom term at level 10) : term_scope.

Notation "+ t" :=
  (Op1Pos t) (in custom term at level 23, t custom term at level 10) : term_scope.

Notation "- t" :=
  (Op1Neg t) (in custom term at level 23, t custom term at level 10) : term_scope.

Notation "'not' t" :=
  (Op1Not t) (in custom term at level 23, t custom term at level 10) : term_scope.

Notation "'lnot' t" :=
  (Op1Lnot t) (in custom term at level 23, t custom term at level 10) : term_scope.

Notation "'fst' t" :=
  (TVFst t) (in custom term at level 23, t custom term at level 10) : term_scope.

Notation "'snd' t" :=
  (TVSnd t) (in custom term at level 23, t custom term at level 10) : term_scope.

Notation "'ref' t" :=
  (TVRef t) (in custom term at level 23, t custom term at level 10) : term_scope.

Notation "'assert' t" :=
  (TVAssert t) (in custom term at level 23, t custom term at level 10) : term_scope.

Notation "t1 + t2" :=
  (Op2Add t1 t2) (in custom term at level 40, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 - t2" :=
  (Op2Sub t1 t2) (in custom term at level 40, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 * t2" :=
  (Op2Mul t1 t2) (in custom term at level 39, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 / t2" :=
  (Op2Div t1 t2) (in custom term at level 39, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 'mod' t2" :=
  (Op2Mod t1 t2) (in custom term at level 39, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 'land' t2" :=
  (Op2Land t1 t2) (in custom term at level 39, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 'lor' t2" :=
  (Op2Lor t1 t2) (in custom term at level 39, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 'lxor' t2" :=
  (Op2Lxor t1 t2) (in custom term at level 39, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 ^ t2" :=
  (Op2Pow t1 t2) (in custom term at level 38, t1 custom term, t2 custom term, right associativity) : term_scope.

Notation "t1 'shl' t2" :=
  (Op2Shl t1 t2) (in custom term at level 38, t1 custom term, t2 custom term, right associativity) : term_scope.

Notation "t1 'shr' t2" :=
  (Op2Shr t1 t2) (in custom term at level 38, t1 custom term, t2 custom term, right associativity) : term_scope.

Notation "t1 = t2" :=
  (Op2Eq t1 t2) (in custom term at level 50, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 < t2" :=
  (Op2Lt t1 t2) (in custom term at level 50, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 <= t2" :=
  (Op2Le t1 t2) (in custom term at level 50, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 > t2" :=
  (Op2Gt t1 t2) (in custom term at level 50, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 >= t2" :=
  (Op2Ge t1 t2) (in custom term at level 50, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 <> t2" :=
  (Op2Neq t1 t2) (in custom term at level 50, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 ++ t2" :=
  (Op2App t1 t2) (in custom term at level 41, t1 custom term, t2 custom term, right associativity) : term_scope.

Notation "t1 && t2" :=
  (TVAnd t1 t2) (in custom term at level 51, t1 custom term, t2 custom term, right associativity) : term_scope.

Notation "t1 || t2" :=
  (TVOr t1 t2) (in custom term at level 51, t1 custom term, t2 custom term, right associativity) : term_scope.

Notation "t1 <- t2" :=
  (TVSet t1 t2) (in custom term at level 66, t1 custom term, t2 custom term, right associativity) : term_scope.

Notation "t1 , t2" :=
  (TVPair t1 t2) (in custom term at level 65, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "'Inl' t" :=
  (TVInl t) (in custom term at level 23, t custom term at level 10) : term_scope.

Notation "'Inr' t" :=
  (TVInr t) (in custom term at level 23, t custom term at level 10) : term_scope.

Notation "'raise' t" :=
  (TRaise t) (in custom term at level 69, t custom term at level 10) : term_scope.

Notation "'try' t1 ;; t2" :=
  (TTry t1 t2) (in custom term at level 69, t1 custom term, t2 custom exn_term) : term_scope.

Notation "'perform' t" :=
  (TPerform t) (in custom term at level 69, t custom term at level 10) : term_scope.

Notation "'handle' t1 ;;; t2" :=
  (THandle t1 TRetNone t2) (in custom term at level 69, t1 custom term, t2 custom eff_term) : term_scope.

Notation "'handle' t1 ;; t2 ;; t3" :=
  (THandle t1 t2 t3) (in custom term at level 69,
        t1 custom term,
        t2 custom ret_term,
        t3 custom eff_term) : term_scope.

Notation "'shallow' 'handle' t1 ;;; t2" :=
  (TShallowHandle t1 TRetNone t2) (in custom term at level 69, t1 custom term, t2 custom eff_term) : term_scope.

Notation "'shallow' 'handle' t1 ;; t2 ;; t3" :=
  (TShallowHandle t1 t2 t3) (in custom term at level 69,
        t1 custom term,
        t2 custom ret_term,
        t3 custom eff_term) : term_scope.

Notation "'by' t" :=
  (TVBy t) (in custom term at level 23, t custom term) : term_scope.

Notation "` l t" :=
  (TVVariant l t) (in custom term at level 23, l constr at level 0, t custom term at level 10) : term_scope.

Notation "t" :=
  (TTupleCons t TTupleNil) (in custom tuple_term at level 0, t custom term at level 64) : term_scope.

Notation "t1 , t2" :=
  (TTupleCons t1 t2) (in custom tuple_term at level 0, t1 custom term at level 64, t2 custom tuple_term at level 0) : term_scope.

Notation "`( t )" :=
  (TVTuple t) (in custom term at level 0, t custom tuple_term at level 0) : term_scope.

Notation "l" :=
  (TRecordCons0 l TRecordNil) (in custom record_term at level 0, l constr at level 0) : term_scope.

Notation "l ; t" :=
  (TRecordCons0 l t) (in custom record_term at level 0, l constr at level 0, t custom record_term at level 0) : term_scope.

Notation "l := t" :=
  (TRecordCons1 l t TRecordNil) (in custom record_term at level 0, l constr at level 0, t custom term at level 65) : term_scope.

Notation "l := t1 ; t2" :=
  (TRecordCons1 l t1 t2) (in custom record_term at level 0,
        l constr at level 0,
        t1 custom term at level 65,
        t2 custom record_term at level 0) : term_scope.

Notation "'..' t" :=
  (TRecordRest t) (in custom record_term at level 0, t custom term at level 65) : term_scope.

Notation "`{ t }" :=
  (TVRecord t) (in custom term at level 0, t custom record_term at level 0) : term_scope.

Notation "t .# i" :=
  (TVProjTuple t i) (in custom term at level 7, t custom term, i constr at level 0, left associativity) : term_scope.

Notation "t .` l" :=
  (TVProjRecord t l) (in custom term at level 7, t custom term, l constr at level 0, left associativity) : term_scope.

Notation "t1 .[ t2 ]" :=
  (TVGetAt t1 t2) (in custom term at level 7, t1 custom term, t2 custom term at level 65, left associativity) : term_scope.

Notation "t1 .[ t2 ] <- t3" :=
  (TVSetAt t1 t2 t3) (in custom term at level 7,
        t1 custom term,
        t2 custom term at level 65,
        t3 custom term at level 65,
        left associativity) : term_scope.

Notation "`[| t1 ; .. ; tn |]" :=
  (TVArray (TArrayCons t1 .. (TArrayCons tn TArrayNil) ..)) (in custom term at level 0,
        t1 custom term at level 65,
        tn custom term at level 65) : term_scope.

From Stdlib Require Import String ZArith.
From shift_reset.core Require Import coerce.

Local Open Scope Z_scope.
Local Open Scope string_scope.
