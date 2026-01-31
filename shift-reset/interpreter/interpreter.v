From Stdlib Require Import Bool String ZArith.
From shift_reset.core Require Import syntax env loc record tag tuple var.
From shift_reset.monad Require Import es_monad.
From shift_reset.interpreter Require Import array builtin error iheap imonad op unwrap.
Import ESMonadNotations.

Local Open Scope Z_scope.
Local Open Scope es_monad_scope.
Local Open Scope lazy_bool_scope.

Definition val_interpreter : Type := val_term -> env -> ixmonad val.
Definition interpreter : Type := term -> env -> kont -> irmonad val.

Fixpoint interpret_val_term (t : val_term) (e : env) : ixmonad val :=
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
      let* b := except_exn_to_ixmonad (unwrap_vbool v) in
      if b then interpret_val_term t2 e else pure VFalse
  | TVOr t1 t2 =>
      let* v := interpret_val_term t1 e in
      let* b := except_exn_to_ixmonad (unwrap_vbool v) in
      if b then pure VTrue else interpret_val_term t2 e
  | TVFun b t' => pure (VFun b t' e)
  | TVFix f b t' => pure (VFix f b t' e)
  | TVFixMut t' f => pure (VFixMut t' f e)
  | TVPair t1 t2 =>
      let* v := interpret_val_term t1 e in
      VPair v <$> interpret_val_term t2 e
  | TVFst t' =>
      let* v := interpret_val_term t' e in
      fst <$> except_exn_to_ixmonad (unwrap_vprod v)
  | TVSnd t' =>
      let* v := interpret_val_term t' e in
      snd <$> except_exn_to_ixmonad (unwrap_vprod v)
  | TVTuple t' => VTuple <$> interpret_tuple_term t' e
  | TVRecord t' => VRecord <$> interpret_record_term t' e
  | TVProj t' l =>
      let* v := interpret_val_term t' e in
      let* r := except_exn_to_ixmonad (unwrap_vrecord v) in
      match record_lookup l r with
      | None => throw (Name_error (tag_car l))
      | Some v' => pure v'
      end
  | TVInl t' => VInl <$> interpret_val_term t' e
  | TVInr t' => VInr <$> interpret_val_term t' e
  | TVVariant l t' => VVariant l <$> interpret_val_term t' e
  | TVExn l t' => VExn l <$> interpret_val_term t' e
  | TVEff l t' => VEff l <$> interpret_val_term t' e
  | TVRef t' =>
      let* v := interpret_val_term t' e in
      state (fun h => (VRef (iheap_next_loc h), iheap_alloc v h))
  | TVArray t' =>
      let* t := interpret_tuple_term t' e in
      state (fun h => (VArray (iheap_next_loc h) (Z.of_nat (tuple_length t)), array_of_tuple_alloc t h))
  | TVGet t' =>
      let* v := interpret_val_term t' e in
      let* l := except_exn_to_ixmonad (unwrap_vref v) in
      let* h := get in
      match iheap_read l h with
      | None => throw (Memory_error "ref_get")
      | Some v' => pure v'
      end
  | TVSet t1 t2 =>
      let* v1 := interpret_val_term t1 e in
      let* v2 := interpret_val_term t2 e in
      let* l := except_exn_to_ixmonad (unwrap_vref v1) in
      let* h := get in
      match iheap_write l v2 h with
      | None => throw (Memory_error "ref_set")
      | Some h' => VTt <$ put h'
      end
  | TVGetAt t1 t2 =>
      let* v1 := interpret_val_term t1 e in
      let* v2 := interpret_val_term t2 e in
      let* '(Array l z) := except_exn_to_ixmonad (unwrap_varray v1) in
      let* i := except_exn_to_ixmonad (unwrap_vint v2) in
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
      let* '(Array l z) := except_exn_to_ixmonad (unwrap_varray v1) in
      let* i := except_exn_to_ixmonad (unwrap_vint v2) in
      if (i <? 0) ||| (z <=? i) then
        throw (Invalid_argument "index out of bounds")
      else
        let* h := get in
        match iheap_write (loc_add l (Z.to_N i)) v3 h with
        | None => throw (Memory_error "array_set_at")
        | Some h' => VTt <$ put h'
        end
  | TVAssert t' =>
      let* v := interpret_val_term t' e in
      let* b := except_exn_to_ixmonad (unwrap_vbool v) in
      if b then pure VTt else throw (Assert_failure "")
  | TVOp1 op t' =>
      let* v := interpret_val_term t' e in
      except_exn_to_ixmonad (dispatch_op1 op v)
  | TVOp2 op t1 t2 =>
      let* v1 := interpret_val_term t1 e in
      let* v2 := interpret_val_term t2 e in
      except_exn_to_ixmonad (dispatch_op2 op v1 v2)
  | TVBuiltin1 l t' =>
      let* f := except_exn_to_ixmonad (dispatch_builtin1 l) in
      interpret_val_term t' e >>= f
  | TVBuiltin2 l t1 t2 =>
      let* f := except_exn_to_ixmonad (dispatch_builtin2 l) in
      let* v := interpret_val_term t1 e in
      interpret_val_term t2 e >>= f v
  end
with interpret_tuple_term (t : tuple_term) (e : env) : ixmonad tuple :=
  match t with
  | TTupleNil => pure TupleNil
  | TTupleCons t1 t2 =>
      let* v := interpret_val_term t1 e in
      TupleCons v <$> interpret_tuple_term t2 e
  end
with interpret_record_term (t : record_term) (e : env) : ixmonad record :=
  match t with
  | TRecordNil => pure RecordNil
  | TRecordCons l t1 t2 =>
      let* v := interpret_val_term t1 e in
      RecordCons l v <$> interpret_record_term t2 e
  end.

Definition interpret_val_term' (t : val_term) (e : env) : irmonad val :=
  ixmonad_to_irmonad (interpret_val_term t e).

Definition with_binder (b : binder) (v : val) (e : env) : env :=
  match b with
  | BAny => e
  | BVar x => ECons x v e
  end.

Definition match_variant (p : variant_pattern) (v : variant) (e : env) : option env :=
  let (l, v) := v in
  match p with
  | PVariantAny => Some e
  | PVariantVar x => Some (ECons x (VVariant l v) e)
  | PVariantTag l' b => if tag_eqb l l' then Some (with_binder b v e) else None
  end.

Definition match_exn (p : variant_pattern) (x : exn) (e : env) : option env :=
  let (l, v) := x in
  match p with
  | PVariantAny => Some e
  | PVariantVar x => Some (ECons x (VExn l v) e)
  | PVariantTag l' b => if tag_eqb l l' then Some (with_binder b v e) else None
  end.

Definition match_eff (p : variant_pattern) (f : eff) (e : env) : option env :=
  let (l, v) := f in
  match p with
  | PVariantAny => Some e
  | PVariantVar x => Some (ECons x (VEff l v) e)
  | PVariantTag l' b => if tag_eqb l l' then Some (with_binder b v e) else None
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
  | PRecordCons l b p' =>
      let (o, r') := record_lookup_remove l r in
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

Fixpoint with_fix_mut_term (t : fix_mut_term) (e : env) : env :=
  match t with
  | TFixMutLast f _ _ => ECons f (VFixMut t f e) e
  | TFixMutCons f _ _ t' => with_fix_mut_term t' (ECons f (VFixMut t f e) e)
  end.

Definition interpret_ret_term (self : interpreter) (t : ret_term) (e : env) (k : kont) (v : val) : irmonad val :=
  match t with
  | TRetNone => pure v
  | TRetSome b t' => self t' (with_binder b v e) k
  end.

Fixpoint interpret_exn_term (self : interpreter) (t : exn_term) (e : env) (k : kont) (x : exn) : option (irmonad val) :=
  match t with
  | TExnLast p t' =>
      match match_exn p x e with
      | Some e' => Some (self t' e' k)
      | None => None
      end
  | TExnCons p t1 t2 =>
      match match_exn p x e with
      | Some e' => Some (self t1 e' k)
      | None => interpret_exn_term self t2 e k x
      end
  end.

Fixpoint interpret_eff_term (self : interpreter) (t : eff_term) (e : env) (k : kont) (f : eff) (u : val) : option (irmonad val) :=
  match t with
  | TEffLast p b t' =>
      match match_eff p f e with
      | Some e' => Some (self t' (with_binder b u e') k)
      | None => None
      end
  | TEffCons p b t1 t2 =>
      match match_eff p f e with
      | Some e' => Some (self t1 (with_binder b u e') k)
      | None => interpret_eff_term self t2 e k f u
      end
  end.

Fixpoint unwind_reset (k : kont) (r : irequest) : irmonad val :=
  match r with
  | IRShift mk f => catch (f (VMKReset mk)) (unwind_reset k)
  | IRControl mk f => throw (IRControl (MKReset mk k) f)
  | IRShift0 mk f => throw (IRShift0 (MKReset mk k) f)
  | IRControl0 mk f => throw (IRControl0 (MKReset mk k) f)
  | IRRaise _ => throw r
  | IRPerform mk f => throw (IRPerform (MKReset mk k) f)
  end.

Fixpoint unwind_prompt (k : kont) (r : irequest) : irmonad val :=
  match r with
  | IRShift mk f => throw (IRShift (MKPrompt mk k) f)
  | IRControl mk f => catch (f (VMKPure mk)) (unwind_prompt k)
  | IRShift0 mk f => throw (IRShift0 (MKPrompt mk k) f)
  | IRControl0 mk f => throw (IRControl0 (MKPrompt mk k) f)
  | IRRaise _ => throw r
  | IRPerform mk f => throw (IRPerform (MKPrompt mk k) f)
  end.

Definition unwind_reset0 (k : kont) (r : irequest) : irmonad val :=
  match r with
  | IRShift mk f => throw (IRShift (MKReset0 mk k) f)
  | IRControl mk f => throw (IRControl (MKReset0 mk k) f)
  | IRShift0 mk f => f (VMKReset0 mk) k
  | IRControl0 mk f => throw (IRControl0 (MKReset0 mk k) f)
  | IRRaise _ => throw r
  | IRPerform mk f => throw (IRPerform (MKReset0 mk k) f)
  end.

Definition unwind_prompt0 (k : kont) (r : irequest) : irmonad val :=
  match r with
  | IRShift mk f => throw (IRShift (MKPrompt0 mk k) f)
  | IRControl mk f => throw (IRControl (MKPrompt0 mk k) f)
  | IRShift0 mk f => throw (IRShift0 (MKPrompt0 mk k) f)
  | IRControl0 mk f => f (VMKPure mk) k
  | IRRaise _ => throw r
  | IRPerform mk f => throw (IRPerform (MKPrompt0 mk k) f)
  end.

Definition unwind_try (self : interpreter) (t : exn_term) (e : env) (k : kont) (r : irequest) : irmonad val :=
  match r with
  | IRShift mk f => throw (IRShift (MKTry mk t e k) f)
  | IRControl mk f => throw (IRControl (MKTry mk t e k) f)
  | IRShift0 mk f => throw (IRShift0 (MKTry mk t e k) f)
  | IRControl0 mk f => throw (IRControl0 (MKTry mk t e k) f)
  | IRRaise x =>
      match interpret_exn_term self t e k x with
      | Some m => m
      | None => throw r
      end
  | IRPerform mk f => throw (IRPerform (MKTry mk t e k) f)
  end.

Definition unwind_handle (self : interpreter) (t1 : ret_term) (t2 : eff_term) (e : env) (k : kont) (m : irequest + val) : irmonad val :=
  match m with
  | inr v => interpret_ret_term self t1 e k v
  | inl r =>
      match r with
      | IRShift mk f => throw (IRShift (MKHandle mk t1 t2 e k) f)
      | IRControl mk f => throw (IRControl (MKHandle mk t1 t2 e k) f)
      | IRShift0 mk f => throw (IRShift0 (MKHandle mk t1 t2 e k) f)
      | IRControl0 mk f => throw (IRControl0 (MKHandle mk t1 t2 e k) f)
      | IRRaise _ => throw r
      | IRPerform mk f =>
          match interpret_eff_term self t2 e k f (VMKHandle mk t1 t2 e) with
          | Some m => m
          | None => throw (IRPerform (MKHandle mk t1 t2 e k) f)
          end
      end
  end.

Definition unwind_shallow_handle (self : interpreter) (t1 : ret_term) (t2 : eff_term) (e : env) (k : kont) (m : irequest + val) : irmonad val :=
  match m with
  | inr v => interpret_ret_term self t1 e k v
  | inl r =>
      match r with
      | IRShift mk f => throw (IRShift (MKShallowHandle mk t1 t2 e k) f)
      | IRControl mk f => throw (IRControl (MKShallowHandle mk t1 t2 e k) f)
      | IRShift0 mk f => throw (IRShift0 (MKShallowHandle mk t1 t2 e k) f)
      | IRControl0 mk f => throw (IRControl0 (MKShallowHandle mk t1 t2 e k) f)
      | IRRaise _ => throw r
      | IRPerform mk f =>
          match interpret_eff_term self t2 e k f (VMKPure mk) with
          | Some m => m
          | None => throw (IRPerform (MKShallowHandle mk t1 t2 e k) f)
          end
      end
  end.

Fixpoint invoke_kont_app (self : interpreter) (k1 : kont) (k2 : kont) (v : val) : irmonad val :=
  match k1 with
  | KNil => pure v
  | KCons0 t e k1' => self t e (KApp k1' k2) >>= invoke_kont_app self k1' k2
  | KCons1 b t e k1' => self t (with_binder b v e) (KApp k1' k2) >>= invoke_kont_app self k1' k2
  | KApp k11 k12 => invoke_kont_app self k11 (KApp k12 k2) v >>= invoke_kont_app self k12 k2
  end.

Fixpoint invoke_kont (self : interpreter) (k : kont) (v : val) : irmonad val :=
  match k with
  | KNil => pure v
  | KCons0 t e k' => self t e k' >>= invoke_kont self k'
  | KCons1 b t e k' => self t (with_binder b v e) k' >>= invoke_kont self k'
  | KApp k1 k2 => invoke_kont_app self k1 k2 v >>= invoke_kont self k2
  end.

Fixpoint invoke_metakont (self : interpreter) (mk : metakont) (v : val) : irmonad val :=
  match mk with
  | MKPure k => invoke_kont self k v
  | MKReset mk' k => catch (invoke_metakont self mk' v) (unwind_reset k) >>= invoke_kont self k
  | MKPrompt mk' k => catch (invoke_metakont self mk' v) (unwind_prompt k) >>= invoke_kont self k
  | MKReset0 mk' k => catch (invoke_metakont self mk' v) (unwind_reset0 k) >>= invoke_kont self k
  | MKPrompt0 mk' k => catch (invoke_metakont self mk' v) (unwind_prompt0 k) >>= invoke_kont self k
  | MKTry mk' t e k => catch (invoke_metakont self mk' v) (unwind_try self t e k) >>= invoke_kont self k
  | MKHandle mk' t1 t2 e k =>
      let* m := try (invoke_metakont self mk' v) in
      unwind_handle self t1 t2 e k m >>= invoke_kont self k
  | MKShallowHandle mk' t1 t2 e k =>
      let* m := try (invoke_metakont self mk' v) in
      unwind_shallow_handle self t1 t2 e k m >>= invoke_kont self k
  end.

Definition invoke_metakont_app (self : interpreter) (mk : metakont) (k : kont) (v : val) : irmonad val :=
  match mk with
  | MKPure k' => invoke_kont_app self k' k v
  | MKReset mk' k' => catch (invoke_metakont self mk' v) (unwind_reset (KApp k' k)) >>= invoke_kont_app self k' k
  | MKPrompt mk' k' => catch (invoke_metakont self mk' v) (unwind_prompt (KApp k' k)) >>= invoke_kont_app self k' k
  | MKReset0 mk' k' => catch (invoke_metakont self mk' v) (unwind_reset0 (KApp k' k)) >>= invoke_kont_app self k' k
  | MKPrompt0 mk' k' => catch (invoke_metakont self mk' v) (unwind_prompt0 (KApp k' k)) >>= invoke_kont_app self k' k
  | MKTry mk' t e k' => catch (invoke_metakont self mk' v) (unwind_try self t e (KApp k' k)) >>= invoke_kont_app self k' k
  | MKHandle mk' t1 t2 e k' =>
      let* m := try (invoke_metakont self mk' v) in
      unwind_handle self t1 t2 e (KApp k' k) m >>= invoke_kont_app self k' k
  | MKShallowHandle mk' t1 t2 e k' =>
      let* m := try (invoke_metakont self mk' v) in
      unwind_shallow_handle self t1 t2 e (KApp k' k) m >>= invoke_kont_app self k' k
  end.

Fixpoint interpret_variant_term (self : interpreter) (t : variant_term) (e : env) (k : kont) (v : variant) : irmonad val :=
  match t with
  | TVariantNil => throw (IRRaise (Match_failure ""))
  | TVariantCons p t1 t2 =>
      match match_variant p v e with
      | Some e' => self t1 e' k
      | None => interpret_variant_term self t2 e k v
      end
  end.

Fixpoint interpret_fix_mut_term (self : interpreter) (t : fix_mut_term) (e : env) (k : kont) (f : var) (v : val) : irmonad val :=
  match t with
  | TFixMutLast f' b t' =>
      if var_eqb f f'
      then self t' (with_binder b v e) k
      else throw (IRRaise (Name_error (var_car f)))
  | TFixMutCons f' b t1 t2 =>
      if var_eqb f f'
      then self t1 (with_binder b v e) k
      else interpret_fix_mut_term self t2 e k f v
  end.

Definition interpret_term'_aux (self : interpreter) : term -> env -> kont -> irmonad val :=
  fix self' t e k :=
    match t with
    | TVal tv => interpret_val_term' tv e
    | TApp tv1 tv2 =>
        let* v1 := interpret_val_term' tv1 e in
        let* v2 := interpret_val_term' tv2 e in
        let* c := except_exn_to_irmonad (unwrap_vclosure v1) in
        match c with
        | CFun b t' e => self t' (with_binder b v2 e) k
        | CFix f b t' e => self t' (with_binder b v2 (ECons f v1 e)) k
        | CFixMut t' f e => interpret_fix_mut_term self t' (with_fix_mut_term t' e) k f v2
        | CMKPure mk => invoke_metakont_app self mk k v2
        | CMKReset mk => catch (invoke_metakont self mk v2) (unwind_reset k)
        | CMKReset0 mk => catch (invoke_metakont self mk v2) (unwind_reset0 k)
        | CMKHandle mk t1 t2 e => try (invoke_metakont self mk v2) >>= unwind_handle self t1 t2 e k
        end
    | TSeq t1 t2 =>
        let* _ := self' t1 e (KCons0 t2 e k) in
        self' t2 e k
    | TLet b t1 t2 =>
        let* v := self' t1 e (KCons1 b t2 e k) in
        self' t2 (with_binder b v e) k
    | TIf tv t1 t2 =>
        let* v := interpret_val_term' tv e in
        let* b := except_exn_to_irmonad (unwrap_vbool v) in
        if b then self' t1 e k else self' t2 e k
    | TSplit b1 b2 tv t' =>
        let* v := interpret_val_term' tv e in
        let* '(v1, v2) := except_exn_to_irmonad (unwrap_vprod v) in
        self' t' (with_binder b2 v2 (with_binder b1 v1 e)) k
    | TCase tv b1 t1 b2 t2 =>
        let* v := interpret_val_term' tv e in
        let* s := except_exn_to_irmonad (unwrap_vsum v) in
        match s with
        | inl v' => self' t1 (with_binder b1 v' e) k
        | inr v' => self' t2 (with_binder b2 v' e) k
        end
    | TWhile tv t' =>
        let* v := interpret_val_term' tv e in
        let* b := except_exn_to_irmonad (unwrap_vbool v) in
        if b then
          let* _ := self' t' e (KCons0 t e k) in
          self t e k
        else pure VTt
    | TFor b tv1 d tv2 t' =>
        let* v1 := interpret_val_term' tv1 e in
        let* v2 := interpret_val_term' tv2 e in
        let* i1 := except_exn_to_irmonad (unwrap_vint v1) in
        let* i2 := except_exn_to_irmonad (unwrap_vint v2) in
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
        in go (Z.to_nat (Z.succ z)) i1
    | TLetFix f b t1 t2 => self' t2 (ECons f (VFix f b t1 e) e) k
    | TLetFixMut t1 t2 => self' t2 (with_fix_mut_term t1 e) k
    | TLetTuple p tv t' =>
        let* v := interpret_val_term' tv e in
        let* t := except_exn_to_irmonad (unwrap_vtuple v) in
        match match_tuple p t e with
        | Some e' => self' t' e' k
        | None => throw (IRRaise (Match_failure ""))
        end
    | TLetRecord p tv t' =>
        let* v := interpret_val_term' tv e in
        let* r := except_exn_to_irmonad (unwrap_vrecord v) in
        match match_record p r e with
        | Some e' => self' t' e' k
        | None => throw (IRRaise (Match_failure ""))
        end
    | TMatchVariant tv t' =>
        let* v := interpret_val_term' tv e in
        except_exn_to_irmonad (unwrap_vvariant v) >>= interpret_variant_term self' t' e k
    | TShift b t' => throw (IRShift (MKPure k) (fun u => self' t' (with_binder b u e) KNil))
    | TControl b t' => throw (IRControl (MKPure k) (fun u => self' t' (with_binder b u e) KNil))
    | TShift0 b t' => throw (IRShift0 (MKPure k) (fun u => self' t' (with_binder b u e)))
    | TControl0 b t' => throw (IRControl0 (MKPure k) (fun u => self' t' (with_binder b u e)))
    | TReset t' => catch (self' t' e KNil) (unwind_reset k)
    | TPrompt t' => catch (self' t' e KNil) (unwind_prompt k)
    | TReset0 t' => catch (self' t' e KNil) (unwind_reset0 k)
    | TPrompt0 t' => catch (self' t' e KNil) (unwind_prompt0 k)
    | TRaise tv =>
        let* v := interpret_val_term' tv e in
        let* x := except_exn_to_irmonad (unwrap_vexn v) in
        throw (IRRaise x)
    | TTry t1 t2 => catch (self' t1 e KNil) (unwind_try self' t2 e k)
    | TPerform tv =>
        let* v := interpret_val_term' tv e in
        let* f := except_exn_to_irmonad (unwrap_veff v) in
        throw (IRPerform (MKPure k) f)
    | THandle t1 t2 t3 => try (self' t1 e KNil) >>= unwind_handle self' t2 t3 e k
    | TShallowHandle t1 t2 t3 => try (self' t1 e KNil) >>= unwind_shallow_handle self' t2 t3 e k
    end.

Fixpoint interpret_term' (fuel : nat) (t : term) (e : env) (k : kont) : irmonad val :=
  match fuel with
  | O => throw (IRRaise Out_of_fuel)
  | S fuel' => interpret_term'_aux (interpret_term' fuel') t e k
  end.

Definition interpret_term (fuel : nat) (t : term) (e : env) (k : kont) : ixmonad val :=
  irmonad_to_ixmonad (interpret_term' fuel t e k).

Definition run_term (fuel : nat) (t : term) : (exn + val) * iheap :=
  run_es_monad (interpret_term fuel t ENil KNil) iheap_empty.

Definition eval_term (fuel : nat) (t : term) : exn + val :=
  fst (run_term fuel t).

Definition exec_term (fuel : nat) (t : term) : iheap :=
  snd (run_term fuel t).
