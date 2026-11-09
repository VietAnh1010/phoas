From shift_reset.core Require Import syntax.

Declare Scope term_scope.
Delimit Scope term_scope with term.
Bind Scope term_scope with comp.
Local Open Scope term_scope.

Declare Custom Entry binder'.
Declare Custom Entry pattern'.
Declare Custom Entry record_pattern.
Declare Custom Entry term.
Declare Custom Entry cases.
Declare Custom Entry fix_mut_defs.
Declare Custom Entry effect_cases.
Declare Custom Entry record_expr.

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

Notation "`( p1 , p2 , p3 , .. , pn )" :=
  (PTuple (PTupleCons p1 (PTupleCons p2 (PTupleCons p3 .. (PTupleCons pn PTupleNil) ..)))) (in custom pattern' at level 0,
        p1 custom pattern' at level 64,
        p2 custom pattern' at level 64,
        p3 custom pattern' at level 64,
        pn custom pattern' at level 64) : term_scope.

Notation "`{ p }" :=
  (PRecord p) (in custom pattern' at level 0, p custom record_pattern at level 1) : term_scope.

Notation "'Inl' p" :=
  (PInl p) (in custom pattern' at level 23, p custom pattern' at level 10) : term_scope.

Notation "'Inr' p" :=
  (PInr p) (in custom pattern' at level 23, p custom pattern' at level 10) : term_scope.

Notation "[ ]" := PNil (in custom pattern' at level 0) : term_scope.

Notation "p1 :: p2" :=
  (PCons p1 p2) (in custom pattern' at level 41, p1 custom pattern', p2 custom pattern', right associativity) : term_scope.

Notation "[ p1 ; .. ; pn ]" :=
  (PCons p1 .. (PCons pn PNil) ..) (in custom pattern' at level 0,
        p1 custom pattern' at level 65,
        pn custom pattern' at level 65) : term_scope.

Notation "` l" :=
  (PVariant (PVariantNone l)) (in custom pattern' at level 23, l constr at level 0) : term_scope.

Notation "` l p" :=
  (PVariant (PVariantSome l p)) (in custom pattern' at level 23, l constr at level 0, p custom pattern' at level 0) : term_scope.

Notation "'..' p" :=
  (PRecordRest p) (in custom record_pattern at level 1, p custom pattern' at level 65) : term_scope.

Notation "l" :=
  (PRecordConsPun l PRecordNil) (in custom record_pattern at level 1, l constr at level 0) : term_scope.

Notation "l ; p" :=
  (PRecordConsPun l p) (in custom record_pattern at level 1, l constr at level 0, p custom record_pattern at level 1) : term_scope.

Notation "l := p" :=
  (PRecordCons l p PRecordNil) (in custom record_pattern at level 1, l constr at level 0, p custom pattern' at level 65) : term_scope.

Notation "l := p1 ; p2" :=
  (PRecordCons l p1 p2) (in custom record_pattern at level 1,
        l constr at level 0,
        p1 custom pattern' at level 65,
        p2 custom record_pattern at level 1) : term_scope.

Notation "<{ t }>" := t (t custom term at level 99) : term_scope.
Notation "( t )" := t (in custom term, t at level 99) : term_scope.
Notation "{ t }" := t (in custom term, t constr) : term_scope.
Notation "t" := t (in custom term at level 0, t constr at level 0) : term_scope.

Notation "| p => t" :=
  (CasesCons p t CasesNil) (in custom cases at level 69, p custom pattern' at level 69, t custom term) : term_scope.

Notation "| p => t1 t2" :=
  (CasesCons p t1 t2) (in custom cases at level 69,
        p custom pattern' at level 69,
        t1 custom term,
        t2 custom cases,
        right associativity) : term_scope.

Notation "| p , k => t" :=
  (EffectCasesCons p k t EffectCasesNil) (in custom effect_cases at level 69,
        p custom pattern' at level 64,
        k custom binder' at level 0,
        t custom term) : term_scope.

Notation "| p , k => t1 t2" :=
  (EffectCasesCons p k t1 t2) (in custom effect_cases at level 69,
        p custom pattern' at level 64,
        k custom binder' at level 0,
        t1 custom term,
        t2 custom effect_cases,
        right associativity) : term_scope.

Notation "t1 t2" :=
  (CApp t1 t2) (in custom term at level 17, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "'if' tv 'then' t1 'else' t2" :=
  (CIf tv t1 t2) (in custom term at level 60,
        tv custom term,
        t1 custom term,
        t2 custom term at level 69) : term_scope.

Notation "t1 ; t2" :=
  (CSeq t1 t2) (in custom term at level 69, t1 custom term, t2 custom term, right associativity) : term_scope.

Notation "'let' p := t1 'in' t2" :=
  (CLet p t1 t2) (in custom term at level 60,
        p custom pattern' at level 0,
        t1 custom term,
        t2 custom term at level 69,
        right associativity) : term_scope.

Notation "'match' tv 'with' t 'end'" :=
  (CMatch tv t) (in custom term at level 0, tv custom term, t custom cases) : term_scope.

Notation "'let' f p1 .. pn := t1 'in' t2" :=
  (CLet f (EFun p1 .. (EFun pn t1) ..) t2) (in custom term at level 60,
        f custom pattern' at level 0,
        p1 custom pattern' at level 0,
        pn custom pattern' at level 0,
        t1 custom term,
        t2 custom term at level 69,
        right associativity) : term_scope.

Notation "'let' 'fix' f p := t1 'in' t2" :=
  (CLetFix f p t1 t2) (in custom term at level 60,
        f constr at level 0,
        p custom pattern' at level 0,
        t1 custom term,
        t2 custom term at level 69,
        right associativity) : term_scope.

Notation "'let' 'fix' f p1 p2 .. pn := t1 'in' t2" :=
  (CLetFix f p1 (EFun p2 .. (EFun pn t1) ..) t2) (in custom term at level 60,
        f constr at level 0,
        p1 custom pattern' at level 0,
        p2 custom pattern' at level 0,
        pn custom pattern' at level 0,
        t1 custom term,
        t2 custom term at level 69,
        right associativity) : term_scope.

Notation "'while' tv 'do' t" :=
  (CWhile tv t) (in custom term at level 60, tv custom term, t custom term at level 68) : term_scope.

Notation "'for' b 'from' tv1 'upto' tv2 'do' t" :=
  (CFor b tv1 Upto tv2 t) (in custom term at level 60,
        b custom binder' at level 0,
        tv1 custom term,
        tv2 custom term,
        t custom term at level 68) : term_scope.

Notation "'for' b 'from' tv1 'downto' tv2 'do' t" :=
  (CFor b tv1 Downto tv2 t) (in custom term at level 60,
        b custom binder' at level 0,
        tv1 custom term,
        tv2 custom term,
        t custom term at level 68) : term_scope.

Notation "'shift' ( 'fun' k => t )" :=
  (CShift k t) (in custom term at level 0, k custom binder' at level 0, t custom term) : term_scope.

Notation "'control' ( 'fun' k => t )" :=
  (CControl k t) (in custom term at level 0, k custom binder' at level 0, t custom term) : term_scope.

Notation "'reset' t" :=
  (CReset t) (in custom term at level 17, t custom term at level 10) : term_scope.

Notation "'prompt' t" :=
  (CPrompt t) (in custom term at level 17, t custom term at level 10) : term_scope.

Notation "'fun' p1 .. pn => t" :=
  (EFun p1 .. (EFun pn t) ..) (in custom term at level 60,
        p1 custom pattern' at level 0,
        pn custom pattern' at level 0,
        t custom term at level 99) : term_scope.

Notation "'fix' f p := t" :=
  (EFix f p t) (in custom term at level 60,
        f constr at level 0,
        p custom pattern' at level 0,
        t custom term at level 99) : term_scope.

Notation "'fix' f p1 p2 .. pn := t" :=
  (EFix f p1 (EFun p2 .. (EFun pn t) ..)) (in custom term at level 60,
        f constr at level 0,
        p1 custom pattern' at level 0,
        p2 custom pattern' at level 0,
        pn custom pattern' at level 0,
        t custom term at level 99) : term_scope.

Notation "f p := t1 'with' t2" :=
  (FixMutCons f p t1 t2) (in custom fix_mut_defs at level 69,
        f constr at level 0,
        p custom pattern' at level 0,
        t1 custom term,
        t2 custom fix_mut_defs) : term_scope.

Notation "f p1 p2 .. pn := t1 'with' t2" :=
  (FixMutCons f p1 (EFun p2 .. (EFun pn t1) ..) t2) (in custom fix_mut_defs at level 69,
        f constr at level 0,
        p1 custom pattern' at level 0,
        p2 custom pattern' at level 0,
        pn custom pattern' at level 0,
        t1 custom term,
        t2 custom fix_mut_defs) : term_scope.

Notation "f p := t" :=
  (FixMutLast f p t) (in custom fix_mut_defs at level 69,
        f constr at level 0,
        p custom pattern' at level 0,
        t custom term) : term_scope.

Notation "f p1 p2 .. pn := t" :=
  (FixMutLast f p1 (EFun p2 .. (EFun pn t) ..)) (in custom fix_mut_defs at level 69,
        f constr at level 0,
        p1 custom pattern' at level 0,
        p2 custom pattern' at level 0,
        pn custom pattern' at level 0,
        t custom term) : term_scope.

Notation "'let' 'fix' f p := t1 'with' t2 'in' t3" :=
  (CLetFixMut (FixMutCons f p t1 t2) t3) (in custom term at level 60,
        f constr at level 0,
        p custom pattern' at level 0,
        t1 custom term,
        t2 custom fix_mut_defs,
        t3 custom term at level 69) : term_scope.

Notation "'let' 'fix' f p1 p2 .. pn := t1 'with' t2 'in' t3" :=
  (CLetFixMut (FixMutCons f p1 (EFun p2 .. (EFun pn t1) ..) t2) t3) (in custom term at level 60,
        f constr at level 0,
        p1 custom pattern' at level 0,
        p2 custom pattern' at level 0,
        pn custom pattern' at level 0,
        t1 custom term,
        t2 custom fix_mut_defs,
        t3 custom term at level 69) : term_scope.

Notation "'fix' f p := t1 'with' t2 'for' g" :=
  (EFixMut (FixMutCons f p t1 t2) g) (in custom term at level 60,
        f constr at level 0,
        p custom pattern' at level 0,
        t1 custom term at level 99,
        t2 custom fix_mut_defs,
        g constr at level 0) : term_scope.

Notation "'fix' f p1 p2 .. pn := t1 'with' t2 'for' g" :=
  (EFixMut (FixMutCons f p1 (EFun p2 .. (EFun pn t1) ..) t2) g) (in custom term at level 60,
        f constr at level 0,
        p1 custom pattern' at level 0,
        p2 custom pattern' at level 0,
        pn custom pattern' at level 0,
        t1 custom term at level 99,
        t2 custom fix_mut_defs,
        g constr at level 0) : term_scope.

Notation "()" := ETt (in custom term at level 0) : term_scope.
Notation "'true'" := ETrue (in custom term at level 0) : term_scope.
Notation "'false'" := EFalse (in custom term at level 0) : term_scope.

Notation "! t" :=
  (EGet t) (in custom term at level 2, t custom term at level 10) : term_scope.

Notation "- t" :=
  (UnOpNeg t) (in custom term at level 23, t custom term at level 10) : term_scope.

Notation "'not' t" :=
  (UnOpNot t) (in custom term at level 17, t custom term at level 10) : term_scope.

Notation "'length' t" :=
  (UnOpLength t) (in custom term at level 17, t custom term at level 10) : term_scope.

Notation "'lnot' t" :=
  (UnOpLnot t) (in custom term at level 17, t custom term at level 10) : term_scope.

Notation "'fst' t" :=
  (EFst t) (in custom term at level 17, t custom term at level 10) : term_scope.

Notation "'snd' t" :=
  (ESnd t) (in custom term at level 17, t custom term at level 10) : term_scope.

Notation "'ref' t" :=
  (ERef t) (in custom term at level 17, t custom term at level 10) : term_scope.

Notation "t1 + t2" :=
  (BinOpAdd t1 t2) (in custom term at level 40, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 - t2" :=
  (BinOpSub t1 t2) (in custom term at level 40, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 * t2" :=
  (BinOpMul t1 t2) (in custom term at level 39, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 / t2" :=
  (BinOpDiv t1 t2) (in custom term at level 39, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 'mod' t2" :=
  (BinOpMod t1 t2) (in custom term at level 39, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 'land' t2" :=
  (BinOpLand t1 t2) (in custom term at level 39, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 'lor' t2" :=
  (BinOpLor t1 t2) (in custom term at level 39, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 'lxor' t2" :=
  (BinOpLxor t1 t2) (in custom term at level 39, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 ^ t2" :=
  (BinOpPow t1 t2) (in custom term at level 38, t1 custom term, t2 custom term, right associativity) : term_scope.

Notation "t1 'shiftl' t2" :=
  (BinOpShiftl t1 t2) (in custom term at level 38, t1 custom term, t2 custom term, right associativity) : term_scope.

Notation "t1 'shiftr' t2" :=
  (BinOpShiftr t1 t2) (in custom term at level 38, t1 custom term, t2 custom term, right associativity) : term_scope.

Notation "t1 = t2" :=
  (BinOpEq t1 t2) (in custom term at level 50, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 < t2" :=
  (BinOpLt t1 t2) (in custom term at level 50, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 <= t2" :=
  (BinOpLe t1 t2) (in custom term at level 50, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 > t2" :=
  (BinOpGt t1 t2) (in custom term at level 50, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 >= t2" :=
  (BinOpGe t1 t2) (in custom term at level 50, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 <> t2" :=
  (BinOpNeq t1 t2) (in custom term at level 50, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "t1 ++ t2" :=
  (BinOpApp t1 t2) (in custom term at level 41, t1 custom term, t2 custom term, right associativity) : term_scope.

Notation "t1 && t2" :=
  (EAnd t1 t2) (in custom term at level 51, t1 custom term, t2 custom term, right associativity) : term_scope.

Notation "t1 || t2" :=
  (EOr t1 t2) (in custom term at level 52, t1 custom term, t2 custom term, right associativity) : term_scope.

Notation "t1 <- t2" :=
  (ESet t1 t2) (in custom term at level 66, t1 custom term, t2 custom term, right associativity) : term_scope.

Notation "t1 , t2" :=
  (EPair t1 t2) (in custom term at level 65, t1 custom term, t2 custom term, left associativity) : term_scope.

Notation "'Inl' t" :=
  (EInl t) (in custom term at level 17, t custom term at level 10) : term_scope.

Notation "'Inr' t" :=
  (EInr t) (in custom term at level 17, t custom term at level 10) : term_scope.

Notation "[ ]" := ENil (in custom term at level 0) : term_scope.

Notation "t1 :: t2" :=
  (ECons t1 t2) (in custom term at level 41, t1 custom term, t2 custom term, right associativity) : term_scope.

Notation "[ t1 ; .. ; tn ]" :=
  (ECons t1 .. (ECons tn ENil) ..) (in custom term at level 0,
        t1 custom term at level 65,
        tn custom term at level 65) : term_scope.

Notation "'raise' t" :=
  (CRaise t) (in custom term at level 17, t custom term at level 10) : term_scope.

Notation "'perform' t" :=
  (CPerform t) (in custom term at level 17, t custom term at level 10) : term_scope.

Notation "'try' t1 'with' t2 'end'" :=
  (CTry t1 t2) (in custom term at level 0, t1 custom term at level 10, t2 custom cases) : term_scope.

Notation "'handle' t1 'with' t2 'end'" :=
  (CHandle t1 (HandleCases ReturnCaseNone t2)) (in custom term at level 0, t1 custom term at level 10, t2 custom effect_cases) : term_scope.

Notation "'handle' t1 'with' '|' 'return' p => t2 t3 'end'" :=
  (CHandle t1 (HandleCases (ReturnCaseSome p t2) t3)) (in custom term at level 0,
        t1 custom term at level 10,
        p custom pattern' at level 69,
        t2 custom term,
        t3 custom effect_cases) : term_scope.

Notation "'shallow' 'handle' t1 'with' t2 'end'" :=
  (CShallowHandle t1 (HandleCases ReturnCaseNone t2)) (in custom term at level 0, t1 custom term at level 10, t2 custom effect_cases) : term_scope.

Notation "'shallow' 'handle' t1 'with' '|' 'return' p => t2 t3 'end'" :=
  (CShallowHandle t1 (HandleCases (ReturnCaseSome p t2) t3)) (in custom term at level 0,
        t1 custom term at level 10,
        p custom pattern' at level 69,
        t2 custom term,
        t3 custom effect_cases) : term_scope.

Notation "'by' t" :=
  (EBy t) (in custom term at level 17, t custom term at level 10) : term_scope.

Notation "` l" :=
  (EVariant (EVariantNone l)) (in custom term at level 17, l constr at level 0) : term_scope.

Notation "` l t" :=
  (EVariant (EVariantSome l t)) (in custom term at level 17, l constr at level 0, t custom term at level 10) : term_scope.

Notation "`( t1 , t2 , t3 , .. , tn )" :=
  (ETuple (EsCons t1 (EsCons t2 (EsCons t3 .. (EsCons tn EsNil) ..)))) (in custom term at level 0,
        t1 custom term at level 64,
        t2 custom term at level 64,
        t3 custom term at level 64,
        tn custom term at level 64) : term_scope.

Notation "l" :=
  (ERecordConsPun l ERecordNil) (in custom record_expr at level 1, l constr at level 0) : term_scope.

Notation "l ; t" :=
  (ERecordConsPun l t) (in custom record_expr at level 1, l constr at level 0, t custom record_expr at level 1) : term_scope.

Notation "l := t" :=
  (ERecordCons l t ERecordNil) (in custom record_expr at level 1, l constr at level 0, t custom term at level 65) : term_scope.

Notation "l := t1 ; t2" :=
  (ERecordCons l t1 t2) (in custom record_expr at level 1,
        l constr at level 0,
        t1 custom term at level 65,
        t2 custom record_expr at level 1) : term_scope.

Notation "'..' t" :=
  (ERecordRest t) (in custom record_expr at level 1, t custom term at level 65) : term_scope.

Notation "`{ t }" :=
  (ERecord t) (in custom term at level 0, t custom record_expr at level 1) : term_scope.

Notation "t .# i" :=
  (EProjTuple t i) (in custom term at level 1, t custom term, i constr at level 0, left associativity) : term_scope.

Notation "t .` l" :=
  (EProjRecord t l) (in custom term at level 1, t custom term, l constr at level 0, left associativity) : term_scope.

Notation "t .`{ r }" :=
  (EUpdateRecord t r) (in custom term at level 1, t custom term, r custom record_expr at level 1, left associativity) : term_scope.

Notation "% l" :=
  (EPrim l) (in custom term at level 1, l constr at level 0) : term_scope.

Notation "t1 .[ t2 ]" :=
  (EGetAt t1 t2) (in custom term at level 1, t1 custom term, t2 custom term at level 65, left associativity) : term_scope.

Notation "t1 .[ t2 ] <- t3" :=
  (ESetAt t1 t2 t3) (in custom term at level 1,
        t1 custom term,
        t2 custom term at level 65,
        t3 custom term at level 65,
        left associativity) : term_scope.

Notation "'array' [ ]" := (EArray EsNil) (in custom term at level 0) : term_scope.

Notation "'array' [ t1 ; .. ; tn ]" :=
  (EArray (EsCons t1 .. (EsCons tn EsNil) ..)) (in custom term at level 0,
        t1 custom term at level 65,
        tn custom term at level 65) : term_scope.

From Stdlib Require Import String ZArith.
From shift_reset.core Require Import coerce.

Local Open Scope Z_scope.
Local Open Scope string_scope.
