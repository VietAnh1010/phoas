From Stdlib Require Import Bool String Qcanon ZArith.
From shift_reset.core Require Import syntax env loc record tag tuple var.
From shift_reset.monad Require Import es_monad.
From shift_reset.interpreter Require Import array builtin ierror iheap op unwrap.
Import ESMonadNotations.

Local Open Scope Z_scope.
Local Open Scope es_monad_scope.
Local Open Scope lazy_bool_scope.

Fixpoint interpret_val_term (t : val_term) (e : env) : es_monad exn iheap val :=
  match t with
  | TVVar x =>
      match env_lookup x e with
      | None => throw (Name_error (var_car x))
      | Some v => pure v
      end
  | TVTt => pure VTt
  | TVInt z => pure (VInt z)
  | TVFloat q => pure (VFloat q)
  | TVTrue => pure VTrue
  | TVFalse => pure VFalse
  | TVChar a => pure (VChar a)
  | TVString s => pure (VString s)
  | TVAnd t1 t2 =>
      let* v := interpret_val_term t1 e in
      let* b := transform (unwrap_vbool v) in
      if b then interpret_val_term t2 e else pure VFalse
  | TVOr t1 t2 =>
      let* v := interpret_val_term t1 e in
      let* b := transform (unwrap_vbool v) in
      if b then pure VTrue else interpret_val_term t2 e
  | TVFun b t' => pure (VFun b t' e)
  | TVFix f b t' => pure (VFix f b t' e)
  | TVFixMut t' f => pure (VFixMut t' f e)
  | TVPair t1 t2 =>
      let* v := interpret_val_term t1 e in
      VPair v <$> interpret_val_term t2 e
  | TVFst t' =>
      let* v := interpret_val_term t' e in
      fst <$> transform (unwrap_vprod v)
  | TVSnd t' =>
      let* v := interpret_val_term t' e in
      snd <$> transform (unwrap_vprod v)
  | TVTuple t' => VTuple <$> interpret_tuple_term t' e
  | TVRecord t' => VRecord <$> interpret_record_term t' e
  | TVProj t' tag =>
      let* v := interpret_val_term t' e in
      let* r := transform (unwrap_vrecord v) in
      match record_lookup tag r with
      | None => throw (Name_error (tag_car tag))
      | Some v' => pure v'
      end
  | TVInl t' => VInl <$> interpret_val_term t' e
  | TVInr t' => VInr <$> interpret_val_term t' e
  | TVVariant tag t' => VVariant tag <$> interpret_val_term t' e
  | TVRef t' =>
      let* v := interpret_val_term t' e in
      state (fun h => (VRef (iheap_next_loc h), iheap_alloc v h))
  | TVGet t' =>
      let* v := interpret_val_term t' e in
      let* l := transform (unwrap_vref v) in
      let* h := get in
      match iheap_read l h with
      | None => throw (Memory_error "ref_get")
      | Some v' => pure v'
      end
  | TVSet t1 t2 =>
      let* v1 := interpret_val_term t1 e in
      let* v2 := interpret_val_term t2 e in
      let* l := transform (unwrap_vref v1) in
      let* h := get in
      match iheap_write l v2 h with
      | None => throw (Memory_error "ref_set")
      | Some h' => VTt <$ put h'
      end
  | TVGetAt t1 t2 =>
      let* v1 := interpret_val_term t1 e in
      let* v2 := interpret_val_term t2 e in
      let* '(Array l z) := transform (unwrap_varray v1) in
      let* i := transform (unwrap_vint v2) in
      if (i <? 0) ||| (z <=? i) then
        throw (Invalid_argument "index out of bounds")
      else
        let* h := get in
        match iheap_read (loc_add l (Z.to_N i)) h with
        | None => throw (Memory_error "array_get_at")
        | Some v => pure v
        end
  | TVSetAt t1 t2 t3 =>
      let* v1 := interpret_val_term t1 e in
      let* v2 := interpret_val_term t2 e in
      let* v3 := interpret_val_term t3 e in
      let* '(Array l z) := transform (unwrap_varray v1) in
      let* i := transform (unwrap_vint v2) in
      if (i <? 0) ||| (z <=? i) then
        throw (Invalid_argument "index out of bounds")
      else
        let* h := get in
        match iheap_write (loc_add l (Z.to_N i)) v3 h with
        | None => throw (Memory_error "array_set_at")
        | Some h' => VTt <$ put h'
        end
  | TVExn tag t' => VExn tag <$> interpret_val_term t' e
  | TVEff tag t' => VEff tag <$> interpret_val_term t' e
  | TVAssert t' =>
      let* v := interpret_val_term t' e in
      let* b := transform (unwrap_vbool v) in
      if b then pure VTt else throw (Assert_failure "")
  | TVArray t' =>
      let* t := interpret_tuple_term t' e in
      state (fun h => (VArray (iheap_next_loc h) (Z.of_nat (tuple_length t)), array_of_tuple_alloc t h))
  | TVOp1 op t' =>
      let* v := interpret_val_term t' e in
      transform (dispatch_op1 op v)
  | TVOp2 op t1 t2 =>
      let* v1 := interpret_val_term t1 e in
      let* v2 := interpret_val_term t2 e in
      transform (dispatch_op2 op v1 v2)
  | TVBuiltin1 tag t' =>
      let* f := transform (dispatch_builtin1 tag) in
      interpret_val_term t' e >>= f
  | TVBuiltin2 tag t1 t2 =>
      let* f := transform (dispatch_builtin2 tag) in
      let* v := interpret_val_term t1 e in
      interpret_val_term t2 e >>= f v
  end
with interpret_tuple_term (t : tuple_term) (e : env) : es_monad exn iheap tuple :=
  match t with
  | TTupleNil => pure TupleNil
  | TTupleCons t1 t2 =>
      let* v := interpret_val_term t1 e in
      TupleCons v <$> interpret_tuple_term t2 e
  end
with interpret_record_term (t : record_term) (e : env) : es_monad exn iheap record :=
  match t with
  | TRecordNil => pure RecordNil
  | TRecordCons tag t1 t2 =>
      let* v := interpret_val_term t1 e in
      RecordCons tag v <$> interpret_record_term t2 e
  end.

Definition with_binder (b : binder) (v : val) (e : env) : env :=
  match b with
  | BAny => e
  | BVar x => ECons x v e
  end.

Definition match_variant (p : variant_pattern) (tag : tag) (v : val) (e : env) : option env :=
  match p with
  | PVariantAny => Some e
  | PVariantVar x => Some (ECons x (VVariant tag v) e)
  | PVariantTag tag' b => if tag_eqb tag tag' then Some (with_binder b v e) else None
  end.

Definition match_exn (p : variant_pattern) (tag : tag) (v : val) (e : env) : option env :=
  match p with
  | PVariantAny => Some e
  | PVariantVar x => Some (ECons x (VExn tag v) e)
  | PVariantTag tag' b => if tag_eqb tag tag' then Some (with_binder b v e) else None
  end.

Definition match_eff (p : variant_pattern) (tag : tag) (v : val) (e : env) : option env :=
  match p with
  | PVariantAny => Some e
  | PVariantVar x => Some (ECons x (VEff tag v) e)
  | PVariantTag tag' b => if tag_eqb tag tag' then Some (with_binder b v e) else None
  end.

Fixpoint match_tuple (p : tuple_pattern) (t : tuple) (e : env) : option env :=
  match p with
  | PTupleNil =>
      match t with
      | TupleNil => Some e
      | TupleCons _ _ => None
      end
  | PTupleCons b p' =>
      match t with
      | TupleNil => None
      | TupleCons v t' => match_tuple p' t' (with_binder b v e)
      end
  end.

Fixpoint match_record (p : record_pattern) (r : record) (e : env) : option env :=
  match p with
  | PRecordAny => Some e
  | PRecordVar x => Some (ECons x (VRecord r) e)
  | PRecordNil =>
      match r with
      | RecordNil => Some e
      | RecordCons _ _ _ => None
      end
  | PRecordCons tag b p' =>
      let (o, r') := record_lookup_remove tag r in
      match o with
      | Some v => match_record p' r' (with_binder b v e)
      | None => None
      end
  end.

Definition with_for_direction (d : for_direction) (i1 i2 : Z) : (Z -> Z) * Z :=
  match d with
  | Upto => (Z.succ, i2 - i1)
  | Downto => (Z.pred, i1 - i2)
  end.

Definition with_fix_mut_term (t : fix_mut_term) (e : env) : env :=
  let fix go t' e' :=
    match t' with
    | TFixMutLast f _ _ => ECons f (VFixMut t f e) e'
    | TFixMutCons f _ _ t'' => go t'' (ECons f (VFixMut t f e) e')
    end
  in
  go t e.

Inductive iresult : Type :=
| IRShift : metakont -> (val -> es_monad iresult iheap val) -> iresult
| IRControl : metakont -> (val -> es_monad iresult iheap val) -> iresult
| IRRaise : tag -> val -> iresult
| IRPerform : metakont -> tag -> val -> iresult.

Definition IRRaise' (exn : exn) : iresult :=
  let (tag, v) := exn in IRRaise tag v.

Definition interpreter : Type := term -> env -> kont -> es_monad iresult iheap val.

Definition interpret_ret_term (self : interpreter) (t : ret_term) (e : env) (k : kont) (v : val) : es_monad iresult iheap val :=
  match t with
  | TRetNone => pure v
  | TRetSome b t' => self t' (with_binder b v e) k
  end.

Fixpoint interpret_exn_term (self : interpreter) (t : exn_term) (e : env) (k : kont) (tag : tag) (v : val) : option (es_monad iresult iheap val) :=
  match t with
  | TExnLast p t' =>
      match match_exn p tag v e with
      | Some e' => Some (self t' e' k)
      | None => None
      end
  | TExnCons p t1 t2 =>
      match match_exn p tag v e with
      | Some e' => Some (self t1 e' k)
      | None => interpret_exn_term self t2 e k tag v
      end
  end.

Fixpoint interpret_eff_term (self : interpreter) (t : eff_term) (e : env) (k : kont) (tag : tag) (v u : val) : option (es_monad iresult iheap val) :=
  match t with
  | TEffLast p b t' =>
      match match_eff p tag v e with
      | Some e' => Some (self t' (with_binder b u e') k)
      | None => None
      end
  | TEffCons p b t1 t2 =>
      match match_eff p tag v e with
      | Some e' => Some (self t1 (with_binder b u e') k)
      | None => interpret_eff_term self t2 e k tag v u
      end
  end.

Fixpoint unwind_reset (k : kont) (r : iresult) : es_monad iresult iheap val :=
  match r with
  | IRShift mk f => catch (f (VMKReset mk)) (unwind_reset k)
  | IRControl mk f => throw (IRControl (MKReset mk k) f)
  | IRRaise _ _ => throw r
  | IRPerform mk tag v => throw (IRPerform (MKReset mk k) tag v)
  end.

Fixpoint unwind_prompt (k : kont) (r : iresult) : es_monad iresult iheap val :=
  match r with
  | IRShift mk f => throw (IRShift (MKPrompt mk k) f)
  | IRControl mk f => catch (f (VMKPure mk)) (unwind_prompt k)
  | IRRaise _ _ => throw r
  | IRPerform mk tag v => throw (IRPerform (MKPrompt mk k) tag v)
  end.

Definition unwind_try (self : interpreter) (t : exn_term) (e : env) (k : kont) (r : iresult) : es_monad iresult iheap val :=
  match r with
  | IRShift mk f => throw (IRShift (MKTry mk t e k) f)
  | IRControl mk f => throw (IRControl (MKTry mk t e k) f)
  | IRRaise tag v =>
      match interpret_exn_term self t e k tag v with
      | Some m => m
      | None => throw r
      end
  | IRPerform mk tag v => throw (IRPerform (MKTry mk t e k) tag v)
  end.

Definition unwind_handle (self : interpreter) (t1 : ret_term) (t2 : eff_term) (e : env) (k : kont) (m : iresult + val) : es_monad iresult iheap val :=
  match m with
  | inr v => interpret_ret_term self t1 e k v
  | inl r =>
      match r with
      | IRShift mk f => throw (IRShift (MKHandle mk t1 t2 e k) f)
      | IRControl mk f => throw (IRControl (MKHandle mk t1 t2 e k) f)
      | IRRaise _ _ => throw r
      | IRPerform mk tag v =>
          match interpret_eff_term self t2 e k tag v (VMKHandle mk t1 t2 e) with
          | Some m => m
          | None => throw (IRPerform (MKHandle mk t1 t2 e k) tag v)
          end
      end
  end.

Definition unwind_shallow_handle (self : interpreter) (t1 : ret_term) (t2 : eff_term) (e : env) (k : kont) (m : iresult + val) : es_monad iresult iheap val :=
  match m with
  | inr v => interpret_ret_term self t1 e k v
  | inl r =>
      match r with
      | IRShift mk f => throw (IRShift (MKShallowHandle mk t1 t2 e k) f)
      | IRControl mk f => throw (IRControl (MKShallowHandle mk t1 t2 e k) f)
      | IRRaise _ _ => throw r
      | IRPerform mk tag v =>
          match interpret_eff_term self t2 e k tag v (VMKPure mk) with
          | Some m => m
          | None => throw (IRPerform (MKShallowHandle mk t1 t2 e k) tag v)
          end
      end
  end.

Fixpoint refine_kont_app (self : interpreter) (k1 : kont) (k2 : kont) (v : val) : es_monad iresult iheap val :=
  match k1 with
  | KNil => pure v
  | KCons0 t e k1' => self t e (KApp k1' k2) >>= refine_kont_app self k1' k2
  | KCons1 b t e k1' => self t (with_binder b v e) (KApp k1' k2) >>= refine_kont_app self k1' k2
  | KApp k11 k12 => refine_kont_app self k11 (KApp k12 k2) v >>= refine_kont_app self k12 k2
  end.

Fixpoint refine_kont (self : interpreter) (k : kont) (v : val) : es_monad iresult iheap val :=
  match k with
  | KNil => pure v
  | KCons0 t e k' => self t e k' >>= refine_kont self k'
  | KCons1 b t e k' => self t (with_binder b v e) k' >>= refine_kont self k'
  | KApp k1 k2 => refine_kont_app self k1 k2 v >>= refine_kont self k2
  end.

Fixpoint refine_metakont (self : interpreter) (mk : metakont) (v : val) : es_monad iresult iheap val :=
  match mk with
  | MKPure k => refine_kont self k v
  | MKReset mk' k => catch (refine_metakont self mk' v) (unwind_reset k) >>= refine_kont self k
  | MKPrompt mk' k => catch (refine_metakont self mk' v) (unwind_prompt k) >>= refine_kont self k
  | MKTry mk' t e k => catch (refine_metakont self mk' v) (unwind_try self t e k) >>= refine_kont self k
  | MKHandle mk' t1 t2 e k =>
      let* m := try (refine_metakont self mk' v) in
      unwind_handle self t1 t2 e k m >>= refine_kont self k
  | MKShallowHandle mk' t1 t2 e k =>
      let* m := try (refine_metakont self mk' v) in
      unwind_shallow_handle self t1 t2 e k m >>= refine_kont self k
  end.

Definition refine_metakont_app (self : interpreter) (mk : metakont) (k : kont) (v : val) : es_monad iresult iheap val :=
  match mk with
  | MKPure k' => refine_kont_app self k' k v
  | MKReset mk' k' => catch (refine_metakont self mk' v) (unwind_reset (KApp k' k)) >>= refine_kont_app self k' k
  | MKPrompt mk' k' => catch (refine_metakont self mk' v) (unwind_prompt (KApp k' k)) >>= refine_kont_app self k' k
  | MKTry mk' t e k' => catch (refine_metakont self mk' v) (unwind_try self t e (KApp k' k)) >>= refine_kont_app self k' k
  | MKHandle mk' t1 t2 e k' =>
      let* m := try (refine_metakont self mk' v) in
      unwind_handle self t1 t2 e (KApp k' k) m >>= refine_kont_app self k' k
  | MKShallowHandle mk' t1 t2 e k' =>
      let* m := try (refine_metakont self mk' v) in
      unwind_shallow_handle self t1 t2 e (KApp k' k) m >>= refine_kont_app self k' k
  end.

Fixpoint interpret_variant_term (self : interpreter) (t : variant_term) (e : env) (k : kont) (tag : tag) (v : val) : es_monad iresult iheap val :=
  match t with
  | TVariantNil => throw (IRRaise' (Match_failure ""))
  | TVariantCons p t1 t2 =>
      match match_variant p tag v e with
      | Some e' => self t1 e' k
      | None => interpret_variant_term self t2 e k tag v
      end
  end.

Fixpoint interpret_fix_mut_term (self : interpreter) (t : fix_mut_term) (e : env) (k : kont) (f : var) (v : val) : es_monad iresult iheap val :=
  match t with
  | TFixMutLast f' b t' => if var_eqb f f' then self t' (with_binder b v e) k else throw (IRRaise' (Name_error (var_car f)))
  | TFixMutCons f' b t1 t2 => if var_eqb f f' then self t1 (with_binder b v e) k else interpret_fix_mut_term self t2 e k f v
  end.

Definition cast0 {E E' S A} (f : E -> E') (m : es_monad E S A) : es_monad E' S A :=
  ESMonad
    (fun s =>
       let (m, s) := run_es_monad m s in
       match m with
       | inl e => (inl (f e), s)
       | inr x => (inr x, s)
       end).

Definition cast {A} : es_monad exn iheap A -> es_monad iresult iheap A := cast0 IRRaise'.

Definition cast' {A} (m : except.t exn A) : es_monad iresult iheap A :=
  cast (transform m).

Definition interpret_term (self : interpreter) : term -> env -> kont -> es_monad iresult iheap val :=
  fix self' t e k :=
    match t with
    | TVal tv => cast (interpret_val_term tv e)
    | TApp tv1 tv2 =>
        let* v1 := cast (interpret_val_term tv1 e) in
        let* v2 := cast (interpret_val_term tv2 e) in
        let* c := cast' (unwrap_vclosure v1) in
        match c with
        | CFun b t' e => self t' (with_binder b v2 e) k
        | CFix f b t' e => self t' (with_binder b v2 (ECons f v1 e)) k
        | CFixMut t' f e => interpret_fix_mut_term self t' (with_fix_mut_term t' e) k f v2
        | CMKPure mk => refine_metakont_app self mk k v2
        | CMKReset mk => catch (refine_metakont self mk v2) (unwind_reset k)
        | CMKHandle mk t1 t2 e => try (refine_metakont self mk v2) >>= unwind_handle self t1 t2 e k
        end
    | TSeq t1 t2 =>
        let* _ := self' t1 e (KCons0 t2 e k) in
        self' t2 e k
    | TLet b t1 t2 =>
        let* v := self' t1 e (KCons1 b t2 e k) in
        self' t2 (with_binder b v e) k
    | TLetFix f b t1 t2 => self' t2 (ECons f (VFix f b t1 e) e) k
    | TLetFixMut t1 t2 => self' t2 (with_fix_mut_term t1 e) k
    | TLetTuple p tv t' =>
        let* v := cast (interpret_val_term tv e) in
        let* t := cast' (unwrap_vtuple v) in
        match match_tuple p t e with
        | Some e' => self' t' e' k
        | None => throw (IRRaise' (Match_failure ""))
        end
    | TLetRecord p tv t' =>
        let* v := cast (interpret_val_term tv e) in
        let* r := cast' (unwrap_vrecord v) in
        match match_record p r e with
        | Some e' => self' t' e' k
        | None => throw (IRRaise' (Match_failure ""))
        end
    | TIf tv t1 t2 =>
        let* v := cast (interpret_val_term tv e) in
        let* b := cast' (unwrap_vbool v) in
        if b then self' t1 e k else self' t2 e k
    | TSplit b1 b2 tv t' =>
        let* v := cast (interpret_val_term tv e) in
        let* '(v1, v2) := cast' (unwrap_vprod v) in
        self' t' (with_binder b2 v2 (with_binder b1 v1 e)) k
    | TCase tv b1 t1 b2 t2 =>
        let* v := cast (interpret_val_term tv e) in
        let* s := cast' (unwrap_vsum v) in
        match s with
        | inl v' => self' t1 (with_binder b1 v' e) k
        | inr v' => self' t2 (with_binder b2 v' e) k
        end
    | TMatchVariant tv t' =>
        let* v := cast (interpret_val_term tv e) in
        let* '(Variant tag v) := cast' (unwrap_vvariant v) in
        interpret_variant_term self' t' e k tag v
    | TWhile tv t' =>
        let* v := cast (interpret_val_term tv e) in
        let* b := cast' (unwrap_vbool v) in
        if b then
          let* _ := self' t' e (KCons0 t e k) in
          self t e k
        else
          pure VTt
    | TFor b tv1 d tv2 t' =>
        let* v1 := cast (interpret_val_term tv1 e) in
        let* v2 := cast (interpret_val_term tv2 e) in
        let* i1 := cast' (unwrap_vint v1) in
        let* i2 := cast' (unwrap_vint v2) in
        let tv := TVInt i2 in
        let (f, z) := with_for_direction d i1 i2 in
        let fix go n i :=
          match n with
          | O => pure VTt
          | S n' =>
              let i' := f i in
              let* _ := self' t' (with_binder b (VInt i) e) (KCons0 (TFor b (TVInt i') d tv t') e k) in
              go n' i'
          end
        in
        go (Z.to_nat (Z.succ z)) i1
    | TShift b t' => throw (IRShift (MKPure k) (fun u => self' t' (with_binder b u e) KNil))
    | TReset t' => catch (self' t' e KNil) (unwind_reset k)
    | TControl b t' => throw (IRControl (MKPure k) (fun u => self' t' (with_binder b u e) KNil))
    | TPrompt t' => catch (self' t' e KNil) (unwind_prompt k)
    | TRaise tv =>
        let* v := cast (interpret_val_term tv e) in
        let* '(Exn tag v) := cast' (unwrap_vexn v) in
        throw (IRRaise tag v)
    | TTry t1 t2 => catch (self' t1 e KNil) (unwind_try self' t2 e k)
    | TPerform tv =>
        let* v := cast (interpret_val_term tv e) in
        let* '(Eff tag v) := cast' (unwrap_veff v) in
        throw (IRPerform (MKPure k) tag v)
    | THandle t1 t2 t3 => try (self' t1 e KNil) >>= unwind_handle self' t2 t3 e k
    | TShallowHandle t1 t2 t3 => try (self' t1 e KNil) >>= unwind_shallow_handle self' t2 t3 e k
    end.

Fixpoint interpret_term' (fuel : nat) (t : term) (e : env) (k : kont) : es_monad iresult iheap val :=
  match fuel with
  | O => throw (IRRaise' Out_of_fuel)
  | S fuel' => interpret_term (interpret_term' fuel') t e k
  end.

Definition iresult_to_exn (r : iresult) : exn :=
  match r with
  | IRShift _ _ => Undelimited_shift
  | IRControl _ _ => Undelimited_control
  | IRRaise tag v => Exn tag v
  | IRPerform _ _ _ => Unhandled_effect ""
  end.

Definition cast'' {A} : es_monad iresult iheap A -> es_monad exn iheap A := cast0 iresult_to_exn.

Definition run_term (fuel : nat) (t : term) : (exn + val) * iheap :=
  run_es_monad (cast'' (interpret_term' fuel t ENil KNil)) iheap_empty.

Definition eval_term (fuel : nat) (t : term) : exn + val :=
  fst (run_term fuel t).

Definition exec_term (fuel : nat) (t : term) : iheap :=
  snd (run_term fuel t).
