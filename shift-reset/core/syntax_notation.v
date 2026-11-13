From shift_reset.core Require Import syntax.

Declare Scope term_scope.
Delimit Scope term_scope with term.

Declare Custom Entry binder'.
Declare Custom Entry pattern'.
Declare Custom Entry record_pattern.
Declare Custom Entry term.
Declare Custom Entry cases.
Declare Custom Entry effect_cases.
Declare Custom Entry fix_mut_defs.
Declare Custom Entry record_expr.

(* ********** *)

(* Print Custom Grammar term and Print Custom Grammar pattern'
   list the levels and the associativity of each level. *)

(* ********** *)

Notation "'_'" := BAny (in custom binder' at level 0) : term_scope.
Notation "b" := b (in custom binder' at level 0, b constr at level 0) : term_scope.

(* ********** *)

Notation "( p )" := p (in custom pattern', p at level 99) : term_scope.
Notation "{ p }" := p (in custom pattern', p constr) : term_scope.
Notation "p" := p (in custom pattern' at level 0, p constr at level 0) : term_scope.

Notation "'_'" := PAny (in custom pattern' at level 0) : term_scope.

Notation "p 'as' x" :=
  (PAlias p x) (in custom pattern' at level 67, p custom pattern', x constr at level 0, left associativity) : term_scope.

Notation "p1 | p2" :=
  (POr p1 p2) (in custom pattern' at level 66, p1 custom pattern', p2 custom pattern', right associativity) : term_scope.

Notation "()" := PTt (in custom pattern' at level 0) : term_scope.
Notation "'true'" := PTrue (in custom pattern' at level 0) : term_scope.
Notation "'false'" := PFalse (in custom pattern' at level 0) : term_scope.

Notation "''' s" :=
  (PString s) (in custom pattern' at level 2, s constr at level 0) : term_scope.

Notation "p1 , p2" :=
  (PPair p1 p2) (in custom pattern' at level 65, p1 custom pattern', p2 custom pattern', left associativity) : term_scope.

Notation "`( p1 , p2 , p3 , .. , pn )" :=
  (PTuple (PsCons p1 (PsCons p2 (PsCons p3 .. (PsCons pn PsNil) ..)))) (in custom pattern' at level 0,
        p1 custom pattern' at level 64,
        p2 custom pattern' at level 64,
        p3 custom pattern' at level 64,
        pn custom pattern' at level 64) : term_scope.

Notation "`{ p }" :=
  (PRecord p) (in custom pattern' at level 0, p custom record_pattern at level 1) : term_scope.

Notation "'Inl' p" :=
  (PInl p) (in custom pattern' at level 17, p custom pattern' at level 10) : term_scope.

Notation "'Inr' p" :=
  (PInr p) (in custom pattern' at level 17, p custom pattern' at level 10) : term_scope.

Notation "` l p" :=
  (PVariant l p) (in custom pattern' at level 17, l constr at level 0, p custom pattern' at level 10) : term_scope.

Notation "` l" :=
  (PEnum l) (in custom pattern' at level 17, l constr at level 0) : term_scope.

Notation "[ ]" := PNil (in custom pattern' at level 0) : term_scope.

Notation "p1 :: p2" :=
  (PCons p1 p2) (in custom pattern' at level 41, p1 custom pattern', p2 custom pattern', right associativity) : term_scope.

Notation "[ p1 ; .. ; pn ]" :=
  (PCons p1 .. (PCons pn PNil) ..) (in custom pattern' at level 0,
        p1 custom pattern' at level 65,
        pn custom pattern' at level 65) : term_scope.

(* ********** *)

Notation "'..' p" :=
  (PRecordRest p) (in custom record_pattern at level 1, p custom pattern' at level 65) : term_scope.

Notation "l := p" :=
  (PRecordCons l p PRecordNil) (in custom record_pattern at level 1, l constr at level 0, p custom pattern' at level 65) : term_scope.

Notation "l := p1 ; p2" :=
  (PRecordCons l p1 p2) (in custom record_pattern at level 1,
        l constr at level 0,
        p1 custom pattern' at level 65,
        p2 custom record_pattern at level 1) : term_scope.

Notation "l" :=
  (PRecordConsPun l PRecordNil) (in custom record_pattern at level 1, l constr at level 0) : term_scope.

Notation "l ; p" :=
  (PRecordConsPun l p) (in custom record_pattern at level 1, l constr at level 0, p custom record_pattern at level 1) : term_scope.

(* ********** *)

Notation "<{ t }>" := t (t custom term at level 99) : term_scope.
Notation "( t )" := t (in custom term, t at level 99) : term_scope.
Notation "{ t }" := t (in custom term, t constr) : term_scope.
Notation "t" := t (in custom term at level 0, t constr at level 0) : term_scope.

(* ********** *)

Notation "e1 e2" :=
  (CApp e1 e2) (in custom term at level 17, e1 custom term, e2 custom term, left associativity) : term_scope.

Notation "c1 ; c2" :=
  (CSeq c1 c2) (in custom term at level 69, c1 custom term, c2 custom term, right associativity) : term_scope.

Notation "'let' p := c1 'in' c2" :=
  (CLet p c1 c2) (in custom term at level 60,
        p custom pattern' at level 0,
        c1 custom term,
        c2 custom term at level 99) : term_scope.

Notation "'match' e 'with' cs 'end'" :=
  (CMatch e cs) (in custom term at level 0, e custom term, cs custom cases at level 1) : term_scope.

Notation "'if' e 'then' c1 'else' c2" :=
  (CIf e c1 c2) (in custom term at level 60,
        e custom term,
        c1 custom term,
        c2 custom term at level 69) : term_scope.

Notation "'while' e 'do' c" :=
  (CWhile e c) (in custom term at level 60, e custom term, c custom term at level 68) : term_scope.

Notation "'for' b 'from' e1 'upto' e2 'do' c" :=
  (CFor b e1 Upto e2 c) (in custom term at level 60,
        b custom binder' at level 0,
        e1 custom term,
        e2 custom term,
        c custom term at level 68) : term_scope.

Notation "'for' b 'from' e1 'downto' e2 'do' c" :=
  (CFor b e1 Downto e2 c) (in custom term at level 60,
        b custom binder' at level 0,
        e1 custom term,
        e2 custom term,
        c custom term at level 68) : term_scope.

Notation "'let' f p := c1 'in' c2" :=
  (CLetFun f p c1 c2) (in custom term at level 60,
        f custom pattern' at level 0,
        p custom pattern' at level 0,
        c1 custom term,
        c2 custom term at level 99) : term_scope.

Notation "'let' f p1 p2 .. pn := c1 'in' c2" :=
  (CLetFun f p1 (CReturn (EFun p2 .. (CReturn (EFun pn c1)) ..)) c2) (in custom term at level 60,
        f custom pattern' at level 0,
        p1 custom pattern' at level 0,
        p2 custom pattern' at level 0,
        pn custom pattern' at level 0,
        c1 custom term,
        c2 custom term at level 99) : term_scope.

Notation "'let' 'fix' f p := c1 'in' c2" :=
  (CLetFix f p c1 c2) (in custom term at level 60,
        f constr at level 0,
        p custom pattern' at level 0,
        c1 custom term,
        c2 custom term at level 99) : term_scope.

Notation "'let' 'fix' f p1 p2 .. pn := c1 'in' c2" :=
  (CLetFix f p1 (CReturn (EFun p2 .. (CReturn (EFun pn c1)) ..)) c2) (in custom term at level 60,
        f constr at level 0,
        p1 custom pattern' at level 0,
        p2 custom pattern' at level 0,
        pn custom pattern' at level 0,
        c1 custom term,
        c2 custom term at level 99) : term_scope.

Notation "'let' 'fix' f p := c1 'with' ds 'in' c2" :=
  (CLetFixMut (FixMutCons f p c1 ds) c2) (in custom term at level 60,
        f constr at level 0,
        p custom pattern' at level 0,
        c1 custom term,
        ds custom fix_mut_defs at level 1,
        c2 custom term at level 99) : term_scope.

Notation "'let' 'fix' f p1 p2 .. pn := c1 'with' ds 'in' c2" :=
  (CLetFixMut (FixMutCons f p1 (CReturn (EFun p2 .. (CReturn (EFun pn c1)) ..)) ds) c2) (in custom term at level 60,
        f constr at level 0,
        p1 custom pattern' at level 0,
        p2 custom pattern' at level 0,
        pn custom pattern' at level 0,
        c1 custom term,
        ds custom fix_mut_defs at level 1,
        c2 custom term at level 99) : term_scope.

Notation "'shift' ( 'fun' b => c )" :=
  (CShift b c) (in custom term at level 0, b custom binder' at level 0, c custom term) : term_scope.

Notation "'control' ( 'fun' b => c )" :=
  (CControl b c) (in custom term at level 0, b custom binder' at level 0, c custom term) : term_scope.

Notation "'reset' c" :=
  (CReset c) (in custom term at level 17, c custom term at level 10) : term_scope.

Notation "'prompt' c" :=
  (CPrompt c) (in custom term at level 17, c custom term at level 10) : term_scope.

Notation "'raise' e" :=
  (CRaise e) (in custom term at level 17, e custom term at level 10) : term_scope.

Notation "'perform' e" :=
  (CPerform e) (in custom term at level 17, e custom term at level 10) : term_scope.

Notation "'try' c 'with' cs 'end'" :=
  (CTry c cs) (in custom term at level 0, c custom term at level 10, cs custom cases at level 1) : term_scope.

Notation "'handle' c 'with' cs 'end'" :=
  (CHandle c (HandleCases ReturnCaseNone cs)) (in custom term at level 0,
        c custom term at level 10,
        cs custom effect_cases at level 1) : term_scope.

Notation "'handle' c1 'with' '|' 'return' p => c2 cs 'end'" :=
  (CHandle c1 (HandleCases (ReturnCaseSome p c2) cs)) (in custom term at level 0,
        c1 custom term at level 10,
        p custom pattern',
        c2 custom term,
        cs custom effect_cases at level 1) : term_scope.

Notation "'shallow' 'handle' c 'with' cs 'end'" :=
  (CShallowHandle c (HandleCases ReturnCaseNone cs)) (in custom term at level 0,
        c custom term at level 10,
        cs custom effect_cases at level 1) : term_scope.

Notation "'shallow' 'handle' c1 'with' '|' 'return' p => c2 cs 'end'" :=
  (CShallowHandle c1 (HandleCases (ReturnCaseSome p c2) cs)) (in custom term at level 0,
        c1 custom term at level 10,
        p custom pattern',
        c2 custom term,
        cs custom effect_cases at level 1) : term_scope.

(* ********** *)

Notation "()" := ETt (in custom term at level 0) : term_scope.
Notation "'true'" := ETrue (in custom term at level 0) : term_scope.
Notation "'false'" := EFalse (in custom term at level 0) : term_scope.

Notation "''' s" :=
  (EString s) (in custom term at level 2, s constr at level 0) : term_scope.

Notation "e1 && e2" :=
  (EAnd e1 e2) (in custom term at level 51, e1 custom term, e2 custom term, right associativity) : term_scope.

Notation "e1 || e2" :=
  (EOr e1 e2) (in custom term at level 52, e1 custom term, e2 custom term, right associativity) : term_scope.

Notation "'fun' p => c" :=
  (EFun p c) (in custom term at level 60,
        p custom pattern' at level 0,
        c custom term at level 99) : term_scope.

Notation "'fun' p1 p2 .. pn => c" :=
  (EFun p1 (CReturn (EFun p2 .. (CReturn (EFun pn c)) ..))) (in custom term at level 60,
        p1 custom pattern' at level 0,
        p2 custom pattern' at level 0,
        pn custom pattern' at level 0,
        c custom term at level 99) : term_scope.

Notation "'fix' f p := c" :=
  (EFix f p c) (in custom term at level 60,
        f constr at level 0,
        p custom pattern' at level 0,
        c custom term at level 99) : term_scope.

Notation "'fix' f p1 p2 .. pn := c" :=
  (EFix f p1 (CReturn (EFun p2 .. (CReturn (EFun pn c)) ..))) (in custom term at level 60,
        f constr at level 0,
        p1 custom pattern' at level 0,
        p2 custom pattern' at level 0,
        pn custom pattern' at level 0,
        c custom term at level 99) : term_scope.

Notation "'fix' f1 p := c 'with' ds 'for' f2" :=
  (EFixMut (FixMutCons f1 p c ds) f2) (in custom term at level 60,
        f1 constr at level 0,
        p custom pattern' at level 0,
        c custom term at level 99,
        ds custom fix_mut_defs at level 1,
        f2 constr at level 0) : term_scope.

Notation "'fix' f1 p1 p2 .. pn := c 'with' ds 'for' f2" :=
  (EFixMut (FixMutCons f1 p1 (CReturn (EFun p2 .. (CReturn (EFun pn c)) ..)) ds) f2) (in custom term at level 60,
        f1 constr at level 0,
        p1 custom pattern' at level 0,
        p2 custom pattern' at level 0,
        pn custom pattern' at level 0,
        c custom term at level 99,
        ds custom fix_mut_defs at level 1,
        f2 constr at level 0) : term_scope.

Notation "e1 , e2" :=
  (EPair e1 e2) (in custom term at level 65, e1 custom term, e2 custom term, left associativity) : term_scope.

Notation "`( e1 , e2 , e3 , .. , en )" :=
  (ETuple (EsCons e1 (EsCons e2 (EsCons e3 .. (EsCons en EsNil) ..)))) (in custom term at level 0,
        e1 custom term at level 64,
        e2 custom term at level 64,
        e3 custom term at level 64,
        en custom term at level 64) : term_scope.

Notation "`{ e }" :=
  (ERecord e) (in custom term at level 0, e custom record_expr at level 1) : term_scope.

Notation "'fst' e" :=
  (EFst e) (in custom term at level 17, e custom term at level 10) : term_scope.

Notation "'snd' e" :=
  (ESnd e) (in custom term at level 17, e custom term at level 10) : term_scope.

Notation "e .# n" :=
  (EProjTuple e n) (in custom term at level 1, e custom term, n constr at level 0, left associativity) : term_scope.

Notation "e .` l" :=
  (EProjRecord e l) (in custom term at level 1, e custom term, l constr at level 0, left associativity) : term_scope.

Notation "e1 .`{ e2 }" :=
  (EUpdateRecord e1 e2) (in custom term at level 1, e1 custom term, e2 custom record_expr at level 1, left associativity) : term_scope.

Notation "'Inl' e" :=
  (EInl e) (in custom term at level 17, e custom term at level 10) : term_scope.

Notation "'Inr' e" :=
  (EInr e) (in custom term at level 17, e custom term at level 10) : term_scope.

Notation "` l e" :=
  (EVariant l e) (in custom term at level 17, l constr at level 0, e custom term at level 10) : term_scope.

Notation "` l" :=
  (EEnum l) (in custom term at level 17, l constr at level 0) : term_scope.

Notation "[ ]" := ENil (in custom term at level 0) : term_scope.

Notation "e1 :: e2" :=
  (ECons e1 e2) (in custom term at level 41, e1 custom term, e2 custom term, right associativity) : term_scope.

Notation "[ e1 ; .. ; en ]" :=
  (ECons e1 .. (ECons en ENil) ..) (in custom term at level 0,
        e1 custom term at level 65,
        en custom term at level 65) : term_scope.

Notation "'ref' e" :=
  (ERef e) (in custom term at level 17, e custom term at level 10) : term_scope.

Notation "'array' [ ]" := (EArray EsNil) (in custom term at level 0) : term_scope.

Notation "'array' [ e1 ; .. ; en ]" :=
  (EArray (EsCons e1 .. (EsCons en EsNil) ..)) (in custom term at level 0,
        e1 custom term at level 65,
        en custom term at level 65) : term_scope.

Notation "! e" :=
  (EGet e) (in custom term at level 2, e custom term at level 2) : term_scope.

Notation "e1 <- e2" :=
  (ESet e1 e2) (in custom term at level 66, e1 custom term, e2 custom term, right associativity) : term_scope.

Notation "e1 .[ e2 ]" :=
  (EGetAt e1 e2) (in custom term at level 1, e1 custom term, e2 custom term, left associativity) : term_scope.

Notation "e1 .[ e2 ] <- e3" :=
  (ESetAt e1 e2 e3) (in custom term at level 1,
        e1 custom term,
        e2 custom term,
        e3 custom term at level 66,
        left associativity) : term_scope.

Notation "- e" :=
  (EUnOp UnOpNeg e) (in custom term at level 23, e custom term at level 23) : term_scope.

Notation "'not' e" :=
  (EUnOp UnOpNot e) (in custom term at level 17, e custom term at level 10) : term_scope.

Notation "'lnot' e" :=
  (EUnOp UnOpLnot e) (in custom term at level 17, e custom term at level 10) : term_scope.

Notation "'length' e" :=
  (EUnOp UnOpLength e) (in custom term at level 17, e custom term at level 10) : term_scope.

Notation "e1 + e2" :=
  (EBinOp BinOpAdd e1 e2) (in custom term at level 40, e1 custom term, e2 custom term, left associativity) : term_scope.

Notation "e1 - e2" :=
  (EBinOp BinOpSub e1 e2) (in custom term at level 40, e1 custom term, e2 custom term, left associativity) : term_scope.

Notation "e1 * e2" :=
  (EBinOp BinOpMul e1 e2) (in custom term at level 39, e1 custom term, e2 custom term, left associativity) : term_scope.

Notation "e1 / e2" :=
  (EBinOp BinOpDiv e1 e2) (in custom term at level 39, e1 custom term, e2 custom term, left associativity) : term_scope.

Notation "e1 'mod' e2" :=
  (EBinOp BinOpMod e1 e2) (in custom term at level 39, e1 custom term, e2 custom term, left associativity) : term_scope.

Notation "e1 ^ e2" :=
  (EBinOp BinOpPow e1 e2) (in custom term at level 38, e1 custom term, e2 custom term, right associativity) : term_scope.

Notation "e1 'land' e2" :=
  (EBinOp BinOpLand e1 e2) (in custom term at level 39, e1 custom term, e2 custom term, left associativity) : term_scope.

Notation "e1 'lor' e2" :=
  (EBinOp BinOpLor e1 e2) (in custom term at level 39, e1 custom term, e2 custom term, left associativity) : term_scope.

Notation "e1 'lxor' e2" :=
  (EBinOp BinOpLxor e1 e2) (in custom term at level 39, e1 custom term, e2 custom term, left associativity) : term_scope.

Notation "e1 'shiftl' e2" :=
  (EBinOp BinOpShiftl e1 e2) (in custom term at level 38, e1 custom term, e2 custom term, right associativity) : term_scope.

Notation "e1 'shiftr' e2" :=
  (EBinOp BinOpShiftr e1 e2) (in custom term at level 38, e1 custom term, e2 custom term, right associativity) : term_scope.

Notation "e1 ++ e2" :=
  (EBinOp BinOpAppend e1 e2) (in custom term at level 41, e1 custom term, e2 custom term, right associativity) : term_scope.

Notation "e1 < e2" :=
  (EBinOp BinOpLt e1 e2) (in custom term at level 50, e1 custom term, e2 custom term, left associativity) : term_scope.

Notation "e1 <= e2" :=
  (EBinOp BinOpLe e1 e2) (in custom term at level 50, e1 custom term, e2 custom term, left associativity) : term_scope.

Notation "e1 > e2" :=
  (EBinOp BinOpGt e1 e2) (in custom term at level 50, e1 custom term, e2 custom term, left associativity) : term_scope.

Notation "e1 >= e2" :=
  (EBinOp BinOpGe e1 e2) (in custom term at level 50, e1 custom term, e2 custom term, left associativity) : term_scope.

Notation "e1 = e2" :=
  (EBinOp BinOpEq e1 e2) (in custom term at level 50, e1 custom term, e2 custom term, left associativity) : term_scope.

Notation "e1 <> e2" :=
  (EBinOp BinOpNeq e1 e2) (in custom term at level 50, e1 custom term, e2 custom term, left associativity) : term_scope.

Notation "% l" :=
  (EPrim l) (in custom term at level 2, l constr at level 0) : term_scope.

Notation "'by' c" :=
  (EBy c) (in custom term at level 17, c custom term at level 10) : term_scope.

(* ********** *)

Notation "| p => c" :=
  (CasesCons p c CasesNil) (in custom cases at level 1, p custom pattern', c custom term) : term_scope.

Notation "| p => c cs" :=
  (CasesCons p c cs) (in custom cases at level 1,
        p custom pattern',
        c custom term,
        cs custom cases at level 1) : term_scope.

(* ********** *)

Notation "| p , b => c" :=
  (EffectCasesCons p b c EffectCasesNil) (in custom effect_cases at level 1,
        p custom pattern' at level 64,
        b custom binder' at level 0,
        c custom term) : term_scope.

Notation "| p , b => c cs" :=
  (EffectCasesCons p b c cs) (in custom effect_cases at level 1,
        p custom pattern' at level 64,
        b custom binder' at level 0,
        c custom term,
        cs custom effect_cases at level 1) : term_scope.

(* ********** *)

Notation "f p := c" :=
  (FixMutCons f p c FixMutNil) (in custom fix_mut_defs at level 1,
        f constr at level 0,
        p custom pattern' at level 0,
        c custom term) : term_scope.

Notation "f p1 p2 .. pn := c" :=
  (FixMutCons f p1 (CReturn (EFun p2 .. (CReturn (EFun pn c)) ..)) FixMutNil) (in custom fix_mut_defs at level 1,
        f constr at level 0,
        p1 custom pattern' at level 0,
        p2 custom pattern' at level 0,
        pn custom pattern' at level 0,
        c custom term) : term_scope.

Notation "f p := c 'with' ds" :=
  (FixMutCons f p c ds) (in custom fix_mut_defs at level 1,
        f constr at level 0,
        p custom pattern' at level 0,
        c custom term,
        ds custom fix_mut_defs at level 1) : term_scope.

Notation "f p1 p2 .. pn := c 'with' ds" :=
  (FixMutCons f p1 (CReturn (EFun p2 .. (CReturn (EFun pn c)) ..)) ds) (in custom fix_mut_defs at level 1,
        f constr at level 0,
        p1 custom pattern' at level 0,
        p2 custom pattern' at level 0,
        pn custom pattern' at level 0,
        c custom term,
        ds custom fix_mut_defs at level 1) : term_scope.

(* ********** *)

Notation "'..' e" :=
  (ERecordRest e) (in custom record_expr at level 1, e custom term at level 65) : term_scope.

Notation "l := e" :=
  (ERecordCons l e ERecordNil) (in custom record_expr at level 1, l constr at level 0, e custom term at level 65) : term_scope.

Notation "l := e1 ; e2" :=
  (ERecordCons l e1 e2) (in custom record_expr at level 1,
        l constr at level 0,
        e1 custom term at level 65,
        e2 custom record_expr at level 1) : term_scope.

Notation "l" :=
  (ERecordConsPun l ERecordNil) (in custom record_expr at level 1, l constr at level 0) : term_scope.

Notation "l ; e" :=
  (ERecordConsPun l e) (in custom record_expr at level 1, l constr at level 0, e custom record_expr at level 1) : term_scope.
