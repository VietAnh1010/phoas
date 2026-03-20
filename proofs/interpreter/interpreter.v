From Stdlib Require Import Ascii Bool List String Qcanon ZArith.
From shift_reset.core Require Import syntax env ident loc record tuple.
From shift_reset.monad Require Import es_monad.
From shift_reset.interpreter Require builtin op.
From shift_reset.interpreter Require Import interpreter array error iheap imonad pattern unwrap.
Import ESMonadNotations ListNotations.

Local Open Scope Z_scope.
Local Open Scope es_monad_scope.
Local Open Scope lazy_bool_scope.

Lemma fold_unfold_interpret_tuple_term_TTupleNil :
  forall (self : val_interpreter)
         (e : env),
    interpret_tuple_term self TTupleNil e =
    pure TupleNil.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_tuple_term_TTupleCons :
  forall (self : val_interpreter)
         (t1 : val_term)
         (t2 : tuple_term)
         (e : env),
    interpret_tuple_term self (TTupleCons t1 t2) e =
    let* v := self t1 e in
    TupleCons v <$> interpret_tuple_term self t2 e.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_record_term_TRecordNil :
  forall (self : val_interpreter)
         (e : env),
    interpret_record_term self TRecordNil e =
    pure RecordNil.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_record_term_TRecordRest :
  forall (self : val_interpreter)
         (t' : val_term)
         (e : env),
    interpret_record_term self (TRecordRest t') e =
    let* v := self t' e in
    iv_monad_to_ivh_monad (unwrap_vrecord v).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_record_term_TRecordCons0 :
  forall (self : val_interpreter)
         (l : ident)
         (t' : record_term)
         (e : env),
    interpret_record_term self (TRecordCons0 l t') e =
    match env_find l e with
    | None => throw (Name_error (ident_car l))
    | Some v => RecordCons l v <$> interpret_record_term self t' e
    end.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_record_term_TRecordCons1 :
  forall (self : val_interpreter)
         (l : ident)
         (t1 : val_term)
         (t2 : record_term)
         (e : env),
    interpret_record_term self (TRecordCons1 l t1 t2) e =
    let* v := self t1 e in
    RecordCons l v <$> interpret_record_term self t2 e.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_array_term_TArrayNil :
  forall (self : val_interpreter)
         (e : env),
    interpret_array_term self TArrayNil e =
    pure (O, []).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_array_term_TArrayCons :
  forall (self : val_interpreter)
         (t1 : val_term)
         (t2 : array_term)
         (e : env),
    interpret_array_term self (TArrayCons t1 t2) e =
    let* v := self t1 e in
    let+ '(n, vs) := interpret_array_term self t2 e in
    (S n, v :: vs).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVVar :
  forall (self : interpreter)
         (x : ident)
         (e : env),
    interpret_val_term self (TVVar x) e =
    match env_find x e with
    | None => throw (Name_error (ident_car x))
    | Some v => pure v
    end.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVTt :
  forall (self : interpreter)
         (e : env),
    interpret_val_term self TVTt e =
    pure VTt.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVInt :
  forall (self : interpreter)
         (z : Z)
         (e : env),
    interpret_val_term self (TVInt z) e =
    pure (VInt z).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVFloat :
  forall (self : interpreter)
         (q : Qc)
         (e : env),
    interpret_val_term self (TVFloat q) e =
    pure (VFloat q).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVTrue :
  forall (self : interpreter)
         (e : env),
    interpret_val_term self TVTrue e =
    pure VTrue.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVFalse :
  forall (self : interpreter)
         (e : env),
    interpret_val_term self TVFalse e =
    pure VFalse.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVChar :
  forall (self : interpreter)
         (a : ascii)
         (e : env),
    interpret_val_term self (TVChar a) e =
    pure (VChar a).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVString :
  forall (self : interpreter)
         (s : string)
         (e : env),
    interpret_val_term self (TVString s) e =
    pure (VString s).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVAnd :
  forall (self : interpreter)
         (t1 t2 : val_term)
         (e : env),
    interpret_val_term self (TVAnd t1 t2) e =
    let* v := interpret_val_term self t1 e in
    let* b := iv_monad_to_ivh_monad (unwrap_vbool v) in
    if b then interpret_val_term self t2 e else pure VFalse.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVOr :
  forall (self : interpreter)
         (t1 t2 : val_term)
         (e : env),
    interpret_val_term self (TVOr t1 t2) e =
    let* v := interpret_val_term self t1 e in
    let* b := iv_monad_to_ivh_monad (unwrap_vbool v) in
    if b then pure VTrue else interpret_val_term self t2 e.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVFun :
  forall (self : interpreter)
         (p : pattern)
         (t' : term)
         (e : env),
    interpret_val_term self (TVFun p t') e =
    pure (VFun p t' e).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVFix :
  forall (self : interpreter)
         (f : ident)
         (p : pattern)
         (t' : term)
         (e : env),
    interpret_val_term self (TVFix f p t') e =
    pure (VFix f p t' e).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVFixMut :
  forall (self : interpreter)
         (t' : fix_mut_term)
         (f : ident)
         (e : env),
    interpret_val_term self (TVFixMut t' f) e =
    pure (VFixMut t' f e).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVPair :
  forall (self : interpreter)
         (t1 t2 : val_term)
         (e : env),
    interpret_val_term self (TVPair t1 t2) e =
    let* v := interpret_val_term self t1 e in
    VPair v <$> interpret_val_term self t2 e.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVFst :
  forall (self : interpreter)
         (t' : val_term)
         (e : env),
    interpret_val_term self (TVFst t') e =
    let* v := interpret_val_term self t' e in
    fst <$> iv_monad_to_ivh_monad (unwrap_vprod v).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVSnd :
  forall (self : interpreter)
         (t' : val_term)
         (e : env),
    interpret_val_term self (TVSnd t') e =
    let* v := interpret_val_term self t' e in
    snd <$> iv_monad_to_ivh_monad (unwrap_vprod v).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVTuple :
  forall (self : interpreter)
         (t' : tuple_term)
         (e : env),
    interpret_val_term self (TVTuple t') e =
    VTuple <$> interpret_tuple_term (interpret_val_term self) t' e.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVRecord :
  forall (self : interpreter)
         (t' : record_term)
         (e : env),
    interpret_val_term self (TVRecord t') e =
    VRecord <$> interpret_record_term (interpret_val_term self) t' e.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVProjTuple :
  forall (self : interpreter)
         (t' : val_term)
         (i : nat)
         (e : env),
    interpret_val_term self (TVProjTuple t' i) e =
    let* v := interpret_val_term self t' e in
    let* t := iv_monad_to_ivh_monad (unwrap_vtuple v) in
    match tuple_get i t with
    | None => throw (Invalid_argument "index out of bounds")
    | Some v' => pure v'
    end.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVProjRecord :
  forall (self : interpreter)
         (t' : val_term)
         (l : ident)
         (e : env),
    interpret_val_term self (TVProjRecord t' l) e =
    let* v := interpret_val_term self t' e in
    let* r := iv_monad_to_ivh_monad (unwrap_vrecord v) in
    match record_find l r with
    | None => throw (Name_error (ident_car l))
    | Some v' => pure v'
    end.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVInl :
  forall (self : interpreter)
         (t' : val_term)
         (e : env),
    interpret_val_term self (TVInl t') e =
    VInl <$> interpret_val_term self t' e.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVInr :
  forall (self : interpreter)
         (t' : val_term)
         (e : env),
    interpret_val_term self (TVInr t') e =
    VInr <$> interpret_val_term self t' e.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVVariant :
  forall (self : interpreter)
         (l : ident)
         (t' : val_term)
         (e : env),
    interpret_val_term self (TVVariant l t') e =
    VVariant l <$> interpret_val_term self t' e.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVRef :
  forall (self : interpreter)
         (t' : val_term)
         (e : env),
    interpret_val_term self (TVRef t') e =
    let* v := interpret_val_term self t' e in
    state (fun h => (VRef (iheap_next_loc h), iheap_alloc v h)).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVArray :
  forall (self : interpreter)
         (t' : array_term)
         (e : env),
    interpret_val_term self (TVArray t') e =
    let* '(n, vs) := interpret_array_term (interpret_val_term self) t' e in
    state (fun h => (VArray (iheap_next_loc h) (Z.of_nat n), array_of_list_alloc vs h)).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVGet :
  forall (self : interpreter)
         (t' : val_term)
         (e : env),
    interpret_val_term self (TVGet t') e =
    let* v := interpret_val_term self t' e in
    let* l := iv_monad_to_ivh_monad (unwrap_vref v) in
    let* h := get in
    match iheap_read l h with
    | None => throw (Memory_error "ref_get")
    | Some v' => pure v'
    end.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVSet :
  forall (self : interpreter)
         (t1 t2 : val_term)
         (e : env),
    interpret_val_term self (TVSet t1 t2) e =
    let* v1 := interpret_val_term self t1 e in
    let* v2 := interpret_val_term self t2 e in
    let* l := iv_monad_to_ivh_monad (unwrap_vref v1) in
    let* h := get in
    match iheap_write l v2 h with
    | None => throw (Memory_error "ref_set")
    | Some h' => VTt <$ put h'
    end.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVGetAt :
  forall (self : interpreter)
         (t1 t2 : val_term)
         (e : env),
    interpret_val_term self (TVGetAt t1 t2) e =
    let* v1 := interpret_val_term self t1 e in
    let* v2 := interpret_val_term self t2 e in
    let* '(Array l z) := iv_monad_to_ivh_monad (unwrap_varray v1) in
    let* i := iv_monad_to_ivh_monad (unwrap_vint v2) in
    if (i <? 0) ||| (z <=? i) then
      throw (Invalid_argument "index out of bounds")
    else
      let* h := get in
      match iheap_read (loc_add l i) h with
      | None => throw (Memory_error "array_get_at")
      | Some v => pure v
      end.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVSetAt :
  forall (self : interpreter)
         (t1 t2 t3 : val_term)
         (e : env),
    interpret_val_term self (TVSetAt t1 t2 t3) e =
    let* v1 := interpret_val_term self t1 e in
    let* v2 := interpret_val_term self t2 e in
    let* v3 := interpret_val_term self t3 e in
    let* '(Array l z) := iv_monad_to_ivh_monad (unwrap_varray v1) in
    let* i := iv_monad_to_ivh_monad (unwrap_vint v2) in
    if (i <? 0) ||| (z <=? i) then
      throw (Invalid_argument "index out of bounds")
    else
      let* h := get in
      match iheap_write (loc_add l i) v3 h with
      | None => throw (Memory_error "array_set_at")
      | Some h' => VTt <$ put h'
      end.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVAssert :
  forall (self : interpreter)
         (t' : val_term)
         (e : env),
    interpret_val_term self (TVAssert t') e =
    let* v := interpret_val_term self t' e in
    let* b := iv_monad_to_ivh_monad (unwrap_vbool v) in
    if b then pure VTt else throw (Assert_failure "").
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVOp1 :
  forall (self : interpreter)
         (op : op1)
         (t' : val_term)
         (e : env),
    interpret_val_term self (TVOp1 op t') e =
    let* v := interpret_val_term self t' e in
    iv_monad_to_ivh_monad (op.dispatch_op1 op v).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVOp2 :
  forall (self : interpreter)
         (op : op2)
         (t1 t2 : val_term)
         (e : env),
    interpret_val_term self (TVOp2 op t1 t2) e =
    let* v1 := interpret_val_term self t1 e in
    let* v2 := interpret_val_term self t2 e in
    iv_monad_to_ivh_monad (op.dispatch_op2 op v1 v2).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVBuiltin1 :
  forall (self : interpreter)
         (l : ident)
         (t' : val_term)
         (e : env),
    interpret_val_term self (TVBuiltin1 l t') e =
    let* f := iv_monad_to_ivh_monad (builtin.dispatch_builtin1 l) in
    interpret_val_term self t' e >>= f.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVBuiltin2 :
  forall (self : interpreter)
         (l : ident)
         (t1 t2 : val_term)
         (e : env),
    interpret_val_term self (TVBuiltin2 l t1 t2) e =
    let* f := iv_monad_to_ivh_monad (builtin.dispatch_builtin2 l) in
    let* v := interpret_val_term self t1 e in
    interpret_val_term self t2 e >>= f v.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term_TVBy :
  forall (self : interpreter)
         (t' : term)
         (e : env),
    interpret_val_term self (TVBy t') e =
    irh_monad_to_ivh_monad (self t' e KNil).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_val_term' :
  forall (self : interpreter)
         (t : val_term)
         (e : env),
    interpret_val_term' self t e =
    ivh_monad_to_irh_monad (interpret_val_term self t e).
Proof. reflexivity. Qed.

Lemma fold_unfold_with_fix_mut_term_TFixMutLast :
  forall (f : ident)
         (p : pattern)
         (t' : term)
         (e : env),
    with_fix_mut_term (TFixMutLast f p t') e =
    ECons f (VFixMut (TFixMutLast f p t') f e) e.
Proof. reflexivity. Qed.

Lemma fold_unfold_with_fix_mut_term_TFixMutCons :
  forall (f : ident)
         (p : pattern)
         (t1 : term)
         (t2 : fix_mut_term)
         (e : env),
    with_fix_mut_term (TFixMutCons f p t1 t2) e =
    with_fix_mut_term t2 (ECons f (VFixMut (TFixMutCons f p t1 t2) f e) e).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_match_term_TMatchNil :
  forall (self : interpreter)
         (e : env)
         (k : kont)
         (v : val),
    interpret_match_term self TMatchNil e k v =
    throw (IRRaise (Match_failure "interpret_match_term")).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_match_term_TMatchCons :
  forall (self : interpreter)
         (p : pattern)
         (t1 : term)
         (t2 : match_term)
         (e : env)
         (k : kont)
         (v : val),
    interpret_match_term self (TMatchCons p t1 t2) e k v =
    let* o := iv_monad_to_irh_monad (match_pattern p v e) in
    match o with
    | Some e' => self t1 e' k
    | None => interpret_match_term self t2 e k v
    end.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_fix_mut_term_TFixMutLast :
  forall (self : interpreter)
         (f' : ident)
         (p : pattern)
         (t' : term)
         (e : env)
         (k : kont)
         (f : ident)
         (v : val),
    interpret_fix_mut_term self (TFixMutLast f' p t') e k f v =
    if ident_eqb f f' then
      let* e' := iv_monad_to_irh_monad (match_irrefutable_pattern p v e) in
      self t' e' k
    else throw (IRRaise (Name_error (ident_car f))).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_fix_mut_term_TFixMutCons :
  forall (self : interpreter)
         (f' : ident)
         (p : pattern)
         (t1 : term)
         (t2 : fix_mut_term)
         (e : env)
         (k : kont)
         (f : ident)
         (v : val),
    interpret_fix_mut_term self (TFixMutCons f' p t1 t2) e k f v =
    if ident_eqb f f' then
      let* e' := iv_monad_to_irh_monad (match_irrefutable_pattern p v e) in
      self t1 e' k
    else interpret_fix_mut_term self t2 e k f v.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_ret_term_TRetNone :
  forall (self : interpreter)
         (e : env)
         (k : kont)
         (v : val),
    interpret_ret_term self TRetNone e k v =
    pure v.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_ret_term_TRetSome :
  forall (self : interpreter)
         (p : pattern)
         (t' : term)
         (e : env)
         (k : kont)
         (v : val),
    interpret_ret_term self (TRetSome p t') e k v =
    let* e' := iv_monad_to_irh_monad (match_irrefutable_pattern p v e) in
    self t' e' k.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_exn_term_TExnLast :
  forall (self : interpreter)
         (p : pattern)
         (t' : term)
         (e : env)
         (k : kont)
         (v : val),
    interpret_exn_term self (TExnLast p t') e k v =
    let* o := iv_monad_to_irh_monad (match_pattern p v e) in
    match o with
    | Some e' => self t' e' k
    | None => throw (IRRaise v)
    end.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_exn_term_TExnCons :
  forall (self : interpreter)
         (p : pattern)
         (t1 : term)
         (t2 : exn_term)
         (e : env)
         (k : kont)
         (v : val),
    interpret_exn_term self (TExnCons p t1 t2) e k v =
    let* o := iv_monad_to_irh_monad (match_pattern p v e) in
    match o with
    | Some e' => self t1 e' k
    | None => interpret_exn_term self t2 e k v
    end.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_eff_term_TEffLast :
  forall (self : interpreter)
         (p : pattern)
         (b : binder)
         (t' : term)
         (e : env)
         (k : kont)
         (v u : val)
         (mk : metakont),
    interpret_eff_term self (TEffLast p b t') e k v u mk =
    let* o := iv_monad_to_irh_monad (match_pattern p v e) in
    match o with
    | Some e' => self t' (with_binder b u e') k
    | None => throw (IRPerform mk v)
    end.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_eff_term_TEffCons :
  forall (self : interpreter)
         (p : pattern)
         (b : binder)
         (t1 : term)
         (t2 : eff_term)
         (e : env)
         (k : kont)
         (v u : val)
         (mk : metakont),
    interpret_eff_term self (TEffCons p b t1 t2) e k v u mk =
    let* o := iv_monad_to_irh_monad (match_pattern p v e) in
    match o with
    | Some e' => self t1 (with_binder b u e') k
    | None => interpret_eff_term self t2 e k v u mk
    end.
Proof. reflexivity. Qed.

Lemma fold_unfold_unwind_reset_IRShift :
  forall (k : kont)
         (mk : metakont)
         (f : val -> irh_monad val),
    unwind_reset k (IRShift mk f) =
    catch (f (VMKReset mk)) (unwind_reset k).
Proof. reflexivity. Qed.

Lemma fold_unfold_unwind_reset_IRControl :
  forall (k : kont)
         (mk : metakont)
         (f : val -> irh_monad val),
    unwind_reset k (IRControl mk f) =
    throw (IRControl (MKReset mk k) f).
Proof. reflexivity. Qed.

Lemma fold_unfold_unwind_reset_IRShift0 :
  forall (k : kont)
         (mk : metakont)
         (f : val -> kont -> irh_monad val),
    unwind_reset k (IRShift0 mk f) =
    throw (IRShift0 (MKReset mk k) f).
Proof. reflexivity. Qed.

Lemma fold_unfold_unwind_reset_IRControl0 :
  forall (k : kont)
         (mk : metakont)
         (f : val -> kont -> irh_monad val),
    unwind_reset k (IRControl0 mk f) =
    throw (IRControl0 (MKReset mk k) f).
Proof. reflexivity. Qed.

Lemma fold_unfold_unwind_reset_IRRaise :
  forall (k : kont)
         (v : val),
    unwind_reset k (IRRaise v) =
    throw (IRRaise v).
Proof. reflexivity. Qed.

Lemma fold_unfold_unwind_reset_IRPerform :
  forall (k : kont)
         (mk : metakont)
         (v : val),
    unwind_reset k (IRPerform mk v) =
    throw (IRPerform (MKReset mk k) v).
Proof. reflexivity. Qed.

Lemma fold_unfold_unwind_prompt_IRShift :
  forall (k : kont)
         (mk : metakont)
         (f : val -> irh_monad val),
    unwind_prompt k (IRShift mk f) =
    throw (IRShift (MKPrompt mk k) f).
Proof. reflexivity. Qed.

Lemma fold_unfold_unwind_prompt_IRControl :
  forall (k : kont)
         (mk : metakont)
         (f : val -> irh_monad val),
    unwind_prompt k (IRControl mk f) =
    catch (f (VMKPure mk)) (unwind_prompt k).
Proof. reflexivity. Qed.

Lemma fold_unfold_unwind_prompt_IRShift0 :
  forall (k : kont)
         (mk : metakont)
         (f : val -> kont -> irh_monad val),
    unwind_prompt k (IRShift0 mk f) =
    throw (IRShift0 (MKPrompt mk k) f).
Proof. reflexivity. Qed.

Lemma fold_unfold_unwind_prompt_IRControl0 :
  forall (k : kont)
         (mk : metakont)
         (f : val -> kont -> irh_monad val),
    unwind_prompt k (IRControl0 mk f) =
    throw (IRControl0 (MKPrompt mk k) f).
Proof. reflexivity. Qed.

Lemma fold_unfold_unwind_prompt_IRRaise :
  forall (k : kont)
         (v : val),
    unwind_prompt k (IRRaise v) =
    throw (IRRaise v).
Proof. reflexivity. Qed.

Lemma fold_unfold_unwind_prompt_IRPerform :
  forall (k : kont)
         (mk : metakont)
         (v : val),
    unwind_prompt k (IRPerform mk v) =
    throw (IRPerform (MKPrompt mk k) v).
Proof. reflexivity. Qed.

Lemma fold_unfold_invoke_kont_app_KNil :
  forall (self : interpreter)
         (k2 : kont)
         (v : val),
    invoke_kont_app self KNil k2 v =
    pure v.
Proof. reflexivity. Qed.

Lemma fold_unfold_invoke_kont_app_KCons0 :
  forall (self : interpreter)
         (t : term)
         (e : env)
         (k1' k2 : kont)
         (v : val),
    invoke_kont_app self (KCons0 t e k1') k2 v =
    self t e (KApp k1' k2) >>= invoke_kont_app self k1' k2.
Proof. reflexivity. Qed.

Lemma fold_unfold_invoke_kont_app_KCons1 :
  forall (self : interpreter)
         (p : pattern)
         (t : term)
         (e : env)
         (k1' k2 : kont)
         (v : val),
    invoke_kont_app self (KCons1 p t e k1') k2 v =
    let* e' := iv_monad_to_irh_monad (match_irrefutable_pattern p v e) in
    self t e' (KApp k1' k2) >>= invoke_kont_app self k1' k2.
Proof. reflexivity. Qed.

Lemma fold_unfold_invoke_kont_app_KApp :
  forall (self : interpreter)
         (k11 k12 k2 : kont)
         (v : val),
    invoke_kont_app self (KApp k11 k12) k2 v =
    invoke_kont_app self k11 (KApp k12 k2) v >>= invoke_kont_app self k12 k2.
Proof. reflexivity. Qed.

Lemma fold_unfold_invoke_kont_KNil :
  forall (self : interpreter)
         (v : val),
    invoke_kont self KNil v =
    pure v.
Proof. reflexivity. Qed.

Lemma fold_unfold_invoke_kont_KCons0 :
  forall (self : interpreter)
         (t : term)
         (e : env)
         (k' : kont)
         (v : val),
    invoke_kont self (KCons0 t e k') v =
    self t e k' >>= invoke_kont self k'.
Proof. reflexivity. Qed.

Lemma fold_unfold_invoke_kont_KCons1 :
  forall (self : interpreter)
         (p : pattern)
         (t : term)
         (e : env)
         (k' : kont)
         (v : val),
    invoke_kont self (KCons1 p t e k') v =
    let* e' := iv_monad_to_irh_monad (match_irrefutable_pattern p v e) in
    self t e' k' >>= invoke_kont self k'.
Proof. reflexivity. Qed.

Lemma fold_unfold_invoke_kont_KApp :
  forall (self : interpreter)
         (k1 k2 : kont)
         (v : val),
    invoke_kont self (KApp k1 k2) v =
    invoke_kont_app self k1 k2 v >>= invoke_kont self k2.
Proof. reflexivity. Qed.

Lemma fold_unfold_invoke_metakont_MKPure :
  forall (self : interpreter)
         (k : kont)
         (v : val),
    invoke_metakont self (MKPure k) v =
    invoke_kont self k v.
Proof. reflexivity. Qed.

Lemma fold_unfold_invoke_metakont_MKReset :
  forall (self : interpreter)
         (mk' : metakont)
         (k : kont)
         (v : val),
    invoke_metakont self (MKReset mk' k) v =
    catch (invoke_metakont self mk' v) (unwind_reset k) >>= invoke_kont self k.
Proof. reflexivity. Qed.

Lemma fold_unfold_invoke_metakont_MKPrompt :
  forall (self : interpreter)
         (mk' : metakont)
         (k : kont)
         (v : val),
    invoke_metakont self (MKPrompt mk' k) v =
    catch (invoke_metakont self mk' v) (unwind_prompt k) >>= invoke_kont self k.
Proof. reflexivity. Qed.

Lemma fold_unfold_invoke_metakont_MKReset0 :
  forall (self : interpreter)
         (mk' : metakont)
         (k : kont)
         (v : val),
    invoke_metakont self (MKReset0 mk' k) v =
    catch (invoke_metakont self mk' v) (unwind_reset0 k) >>= invoke_kont self k.
Proof. reflexivity. Qed.

Lemma fold_unfold_invoke_metakont_MKPrompt0 :
  forall (self : interpreter)
         (mk' : metakont)
         (k : kont)
         (v : val),
    invoke_metakont self (MKPrompt0 mk' k) v =
    catch (invoke_metakont self mk' v) (unwind_prompt0 k) >>= invoke_kont self k.
Proof. reflexivity. Qed.

Lemma fold_unfold_invoke_metakont_MKTry :
  forall (self : interpreter)
         (mk' : metakont)
         (t : exn_term)
         (e : env)
         (k : kont)
         (v : val),
    invoke_metakont self (MKTry mk' t e k) v =
    catch (invoke_metakont self mk' v) (unwind_try self t e k) >>= invoke_kont self k.
Proof. reflexivity. Qed.

Lemma fold_unfold_invoke_metakont_MKHandle :
  forall (self : interpreter)
         (mk' : metakont)
         (t1 : ret_term)
         (t2 : eff_term)
         (e : env)
         (k : kont)
         (v : val),
    invoke_metakont self (MKHandle mk' t1 t2 e k) v =
    let* m := try (invoke_metakont self mk' v) in
    unwind_handle self t1 t2 e k m >>= invoke_kont self k.
Proof. reflexivity. Qed.

Lemma fold_unfold_invoke_metakont_MKShallowHandle :
  forall (self : interpreter)
         (mk' : metakont)
         (t1 : ret_term)
         (t2 : eff_term)
         (e : env)
         (k : kont)
         (v : val),
    invoke_metakont self (MKShallowHandle mk' t1 t2 e k) v =
    let* m := try (invoke_metakont self mk' v) in
    unwind_shallow_handle self t1 t2 e k m >>= invoke_kont self k.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_aux_TVal :
  forall (self : interpreter)
         (tv : val_term)
         (e : env)
         (k : kont),
    interpret_term'_aux self (TVal tv) e k =
    interpret_val_term' (interpret_term'_aux self) tv e.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_aux_TApp :
  forall (self : interpreter)
         (tv1 tv2 : val_term)
         (e : env)
         (k : kont),
    interpret_term'_aux self (TApp tv1 tv2) e k =
    let* v1 := interpret_val_term' (interpret_term'_aux self) tv1 e in
    let* v2 := interpret_val_term' (interpret_term'_aux self) tv2 e in
    let* c := iv_monad_to_irh_monad (unwrap_vclosure v1) in
    match c with
    | CFun p t' e =>
        let* e' := iv_monad_to_irh_monad (match_irrefutable_pattern p v2 e) in
        self t' e' k
    | CFix f p t' e =>
        let* e' := iv_monad_to_irh_monad (match_irrefutable_pattern p v2 (ECons f v1 e)) in
        self t' e' k
    | CFixMut t' f e => interpret_fix_mut_term self t' (with_fix_mut_term t' e) k f v2
    | CMKPure mk => invoke_metakont_app self mk k v2
    | CMKReset mk => catch (invoke_metakont self mk v2) (unwind_reset k)
    | CMKReset0 mk => catch (invoke_metakont self mk v2) (unwind_reset0 k)
    | CMKHandle mk t1 t2 e => try (invoke_metakont self mk v2) >>= unwind_handle self t1 t2 e k
    end.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_aux_TSeq :
  forall (self : interpreter)
         (t1 t2 : term)
         (e : env)
         (k : kont),
    interpret_term'_aux self (TSeq t1 t2) e k =
    let* _ := interpret_term'_aux self t1 e (KCons0 t2 e k) in
    interpret_term'_aux self t2 e k.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_aux_TLet :
  forall (self : interpreter)
         (p : pattern)
         (t1 t2 : term)
         (e : env)
         (k : kont),
    interpret_term'_aux self (TLet p t1 t2) e k =
    let* v := interpret_term'_aux self t1 e (KCons1 p t2 e k) in
    let* e' := iv_monad_to_irh_monad (match_irrefutable_pattern p v e) in
    interpret_term'_aux self t2 e' k.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_aux_TMatch :
  forall (self : interpreter)
         (tv : val_term)
         (t' : match_term)
         (e : env)
         (k : kont),
    interpret_term'_aux self (TMatch tv t') e k =
    interpret_val_term' (interpret_term'_aux self) tv e >>= interpret_match_term (interpret_term'_aux self) t' e k.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_aux_TIf :
  forall (self : interpreter)
         (tv : val_term)
         (t1 t2 : term)
         (e : env)
         (k : kont),
    interpret_term'_aux self (TIf tv t1 t2) e k =
    let* v := interpret_val_term' (interpret_term'_aux self) tv e in
    let* b := iv_monad_to_irh_monad (unwrap_vbool v) in
    if b then interpret_term'_aux self t1 e k else interpret_term'_aux self t2 e k.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_aux_TWhile :
  forall (self : interpreter)
         (tv : val_term)
         (t' : term)
         (e : env)
         (k : kont),
    interpret_term'_aux self (TWhile tv t') e k =
    let* v := interpret_val_term' (interpret_term'_aux self) tv e in
    let* b := iv_monad_to_irh_monad (unwrap_vbool v) in
    if b then
      let* _ := interpret_term'_aux self t' e (KCons0 (TWhile tv t') e k) in
      self (TWhile tv t') e k
    else pure VTt.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_aux_TFor :
  forall (self : interpreter)
         (b : binder)
         (tv1 : val_term)
         (d : for_direction)
         (tv2 : val_term)
         (t' : term)
         (e : env)
         (k : kont),
    interpret_term'_aux self (TFor b tv1 d tv2 t') e k =
    let* v1 := interpret_val_term' (interpret_term'_aux self) tv1 e in
    let* v2 := interpret_val_term' (interpret_term'_aux self) tv2 e in
    let* i1 := iv_monad_to_irh_monad (unwrap_vint v1) in
    let* i2 := iv_monad_to_irh_monad (unwrap_vint v2) in
    let tv := TVInt i2 in
    let (f, z) := with_for_direction d i1 i2 in
    let fix go n i :=
      match n with
      | O => pure VTt
      | S n' =>
          let i' := f i in
          let* _ := interpret_term'_aux self t' (with_binder b (VInt i) e) (KCons0 (TFor b (TVInt i') d tv t') e k) in
          go n' i'
      end
    in go (Z.to_nat (z + 1)) i1.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_aux_TLetFix :
  forall (self : interpreter)
         (f : ident)
         (p : pattern)
         (t1 t2 : term)
         (e : env)
         (k : kont),
    interpret_term'_aux self (TLetFix f p t1 t2) e k =
    interpret_term'_aux self t2 (ECons f (VFix f p t1 e) e) k.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_aux_TLetFixMut :
  forall (self : interpreter)
         (t1 : fix_mut_term)
         (t2 : term)
         (e : env)
         (k : kont),
    interpret_term'_aux self (TLetFixMut t1 t2) e k =
    interpret_term'_aux self t2 (with_fix_mut_term t1 e) k.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_aux_TShift :
  forall (self : interpreter)
         (b : binder)
         (t' : term)
         (e : env)
         (k : kont),
    interpret_term'_aux self (TShift b t') e k =
    throw (IRShift (MKPure k) (fun u => interpret_term'_aux self t' (with_binder b u e) KNil)).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_aux_TControl :
  forall (self : interpreter)
         (b : binder)
         (t' : term)
         (e : env)
         (k : kont),
    interpret_term'_aux self (TControl b t') e k =
    throw (IRControl (MKPure k) (fun u => interpret_term'_aux self t' (with_binder b u e) KNil)).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_aux_TShift0 :
  forall (self : interpreter)
         (b : binder)
         (t' : term)
         (e : env)
         (k : kont),
    interpret_term'_aux self (TShift0 b t') e k =
    throw (IRShift0 (MKPure k) (fun u => interpret_term'_aux self t' (with_binder b u e))).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_aux_TControl0 :
  forall (self : interpreter)
         (b : binder)
         (t' : term)
         (e : env)
         (k : kont),
    interpret_term'_aux self (TControl0 b t') e k =
    throw (IRControl0 (MKPure k) (fun u => interpret_term'_aux self t' (with_binder b u e))).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_aux_TReset :
  forall (self : interpreter)
         (t' : term)
         (e : env)
         (k : kont),
    interpret_term'_aux self (TReset t') e k =
    catch (interpret_term'_aux self t' e KNil) (unwind_reset k).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_aux_TPrompt :
  forall (self : interpreter)
         (t' : term)
         (e : env)
         (k : kont),
    interpret_term'_aux self (TPrompt t') e k =
    catch (interpret_term'_aux self t' e KNil) (unwind_prompt k).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_aux_TReset0 :
  forall (self : interpreter)
         (t' : term)
         (e : env)
         (k : kont),
    interpret_term'_aux self (TReset0 t') e k =
    catch (interpret_term'_aux self t' e KNil) (unwind_reset0 k).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_aux_TPrompt0 :
  forall (self : interpreter)
         (t' : term)
         (e : env)
         (k : kont),
    interpret_term'_aux self (TPrompt0 t') e k =
    catch (interpret_term'_aux self t' e KNil) (unwind_prompt0 k).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_aux_TRaise :
  forall (self : interpreter)
         (tv : val_term)
         (e : env)
         (k : kont),
    interpret_term'_aux self (TRaise tv) e k =
    let* v := interpret_val_term' (interpret_term'_aux self) tv e in
    throw (IRRaise v).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_aux_TTry :
  forall (self : interpreter)
         (t1 : term)
         (t2 : exn_term)
         (e : env)
         (k : kont),
    interpret_term'_aux self (TTry t1 t2) e k =
    catch (interpret_term'_aux self t1 e KNil) (unwind_try (interpret_term'_aux self) t2 e k).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_aux_TPerform :
  forall (self : interpreter)
         (tv : val_term)
         (e : env)
         (k : kont),
    interpret_term'_aux self (TPerform tv) e k =
    let* v := interpret_val_term' (interpret_term'_aux self) tv e in
    throw (IRPerform (MKPure k) v).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_aux_THandle :
  forall (self : interpreter)
         (t1 : term)
         (t2 : ret_term)
         (t3 : eff_term)
         (e : env)
         (k : kont),
    interpret_term'_aux self (THandle t1 t2 t3) e k =
    try (interpret_term'_aux self t1 e KNil) >>= unwind_handle (interpret_term'_aux self) t2 t3 e k.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_aux_TShallowHandle :
  forall (self : interpreter)
         (t1 : term)
         (t2 : ret_term)
         (t3 : eff_term)
         (e : env)
         (k : kont),
    interpret_term'_aux self (TShallowHandle t1 t2 t3) e k =
    try (interpret_term'_aux self t1 e KNil) >>= unwind_shallow_handle (interpret_term'_aux self) t2 t3 e k.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_O :
  forall (t : term)
         (e : env)
         (k : kont),
    interpret_term' O t e k =
    throw (IRRaise Out_of_fuel).
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term'_S :
  forall (fuel' : nat)
         (t : term)
         (e : env)
         (k : kont),
    interpret_term' (S fuel') t e k =
    interpret_term'_aux (interpret_term' fuel') t e k.
Proof. reflexivity. Qed.

Lemma fold_unfold_interpret_term :
  forall (fuel : nat)
         (t : term)
         (e : env)
         (k : kont),
    interpret_term fuel t e k =
    irh_monad_to_ivh_monad (interpret_term' fuel t e k).
Proof. reflexivity. Qed.

Create HintDb fold_unfold_interpret_db discriminated.

Hint Rewrite
  fold_unfold_interpret_tuple_term_TTupleNil
  fold_unfold_interpret_tuple_term_TTupleCons
  fold_unfold_interpret_record_term_TRecordNil
  fold_unfold_interpret_record_term_TRecordRest
  fold_unfold_interpret_record_term_TRecordCons0
  fold_unfold_interpret_record_term_TRecordCons1
  fold_unfold_interpret_array_term_TArrayNil
  fold_unfold_interpret_array_term_TArrayCons
  fold_unfold_interpret_val_term_TVVar
  fold_unfold_interpret_val_term_TVTt
  fold_unfold_interpret_val_term_TVInt
  fold_unfold_interpret_val_term_TVFloat
  fold_unfold_interpret_val_term_TVTrue
  fold_unfold_interpret_val_term_TVFalse
  fold_unfold_interpret_val_term_TVChar
  fold_unfold_interpret_val_term_TVString
  fold_unfold_interpret_val_term_TVAnd
  fold_unfold_interpret_val_term_TVOr
  fold_unfold_interpret_val_term_TVFun
  fold_unfold_interpret_val_term_TVFix
  fold_unfold_interpret_val_term_TVFixMut
  fold_unfold_interpret_val_term_TVPair
  fold_unfold_interpret_val_term_TVFst
  fold_unfold_interpret_val_term_TVSnd
  fold_unfold_interpret_val_term_TVTuple
  fold_unfold_interpret_val_term_TVRecord
  fold_unfold_interpret_val_term_TVProjTuple
  fold_unfold_interpret_val_term_TVProjRecord
  fold_unfold_interpret_val_term_TVInl
  fold_unfold_interpret_val_term_TVInr
  fold_unfold_interpret_val_term_TVVariant
  fold_unfold_interpret_val_term_TVRef
  fold_unfold_interpret_val_term_TVArray
  fold_unfold_interpret_val_term_TVGet
  fold_unfold_interpret_val_term_TVSet
  fold_unfold_interpret_val_term_TVGetAt
  fold_unfold_interpret_val_term_TVSetAt
  fold_unfold_interpret_val_term_TVAssert
  fold_unfold_interpret_val_term_TVOp1
  fold_unfold_interpret_val_term_TVOp2
  fold_unfold_interpret_val_term_TVBuiltin1
  fold_unfold_interpret_val_term_TVBuiltin2
  fold_unfold_interpret_val_term_TVBy
  fold_unfold_interpret_val_term'
  fold_unfold_interpret_match_term_TMatchNil
  fold_unfold_interpret_match_term_TMatchCons
  fold_unfold_interpret_fix_mut_term_TFixMutLast
  fold_unfold_interpret_fix_mut_term_TFixMutCons
  fold_unfold_interpret_ret_term_TRetNone
  fold_unfold_interpret_ret_term_TRetSome
  fold_unfold_interpret_exn_term_TExnLast
  fold_unfold_interpret_exn_term_TExnCons
  fold_unfold_interpret_eff_term_TEffLast
  fold_unfold_interpret_eff_term_TEffCons
  fold_unfold_interpret_term'_aux_TVal
  fold_unfold_interpret_term'_aux_TApp
  fold_unfold_interpret_term'_aux_TSeq
  fold_unfold_interpret_term'_aux_TLet
  fold_unfold_interpret_term'_aux_TMatch
  fold_unfold_interpret_term'_aux_TIf
  fold_unfold_interpret_term'_aux_TWhile
  fold_unfold_interpret_term'_aux_TFor
  fold_unfold_interpret_term'_aux_TLetFix
  fold_unfold_interpret_term'_aux_TLetFixMut
  fold_unfold_interpret_term'_aux_TShift
  fold_unfold_interpret_term'_aux_TControl
  fold_unfold_interpret_term'_aux_TShift0
  fold_unfold_interpret_term'_aux_TControl0
  fold_unfold_interpret_term'_aux_TReset
  fold_unfold_interpret_term'_aux_TPrompt
  fold_unfold_interpret_term'_aux_TReset0
  fold_unfold_interpret_term'_aux_TPrompt0
  fold_unfold_interpret_term'_aux_TRaise
  fold_unfold_interpret_term'_aux_TTry
  fold_unfold_interpret_term'_aux_TPerform
  fold_unfold_interpret_term'_aux_THandle
  fold_unfold_interpret_term'_aux_TShallowHandle
  fold_unfold_interpret_term'_O
  fold_unfold_interpret_term'_S
  fold_unfold_interpret_term
  : fold_unfold_interpret_db.
