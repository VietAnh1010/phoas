From Stdlib Require Import Bool List String ZArith.
From shift_reset.core Require Import syntax env ident loc record tuple.
From shift_reset.monad Require Import es_monad.
From shift_reset.interpreter Require builtin op pattern.
From shift_reset.interpreter Require Import array error iheap imonad unwrap.
Import ESMonadNotations ListNotations.

Local Open Scope Z_scope.
Local Open Scope es_monad_scope.
Local Open Scope lazy_bool_scope.

Definition val_interpreter : Type := val_term -> env -> ivh_monad val.
Definition interpreter : Type := term -> env -> kont -> irh_monad val.

Fixpoint interpret_tuple_term (self : val_interpreter) (t : tuple_term) (e : env) : ivh_monad tuple :=
  match t with
  | TTupleNil => pure TupleNil
  | TTupleCons t1 t2 =>
      let* v := self t1 e in
      TupleCons v <$> interpret_tuple_term self t2 e
  end.

Fixpoint interpret_record_term (self : val_interpreter) (t : record_term) (e : env) : ivh_monad record :=
  match t with
  | TRecordNil => pure RecordNil
  | TRecordRest t' =>
      let* v := self t' e in
      iv_monad_to_ivh_monad (unwrap_vrecord v)
  | TRecordCons0 l t' =>
      match env_lookup l e with
      | None => throw (Name_error (ident_car l))
      | Some v => RecordCons l v <$> interpret_record_term self t' e
      end
  | TRecordCons1 l t1 t2 =>
      let* v := self t1 e in
      RecordCons l v <$> interpret_record_term self t2 e
  end.

Fixpoint interpret_array_term (self : val_interpreter) (t : array_term) (e : env) : ivh_monad (nat * list val) :=
  match t with
  | TArrayNil => pure (O, [])
  | TArrayCons t1 t2 =>
      let* v := self t1 e in
      let+ '(n, vs) := interpret_array_term self t2 e in
      (S n, v :: vs)
  end.

Definition interpret_val_term (self : interpreter) : val_term -> env -> ivh_monad val :=
  fix self' t e :=
    match t with
    | TVVar x =>
        match env_lookup x e with
        | None => throw (Name_error (ident_car x))
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
        let* v := self' t1 e in
        let* b := iv_monad_to_ivh_monad (unwrap_vbool v) in
        if b then self' t2 e else pure VFalse
    | TVOr t1 t2 =>
        let* v := self' t1 e in
        let* b := iv_monad_to_ivh_monad (unwrap_vbool v) in
        if b then pure VTrue else self' t2 e
    | TVFun p t' => pure (VFun p t' e)
    | TVFix f p t' => pure (VFix f p t' e)
    | TVFixMut t' f => pure (VFixMut t' f e)
    | TVPair t1 t2 =>
        let* v := self' t1 e in
        VPair v <$> self' t2 e
    | TVFst t' =>
        let* v := self' t' e in
        fst <$> iv_monad_to_ivh_monad (unwrap_vprod v)
    | TVSnd t' =>
        let* v := self' t' e in
        snd <$> iv_monad_to_ivh_monad (unwrap_vprod v)
    | TVTuple t' => VTuple <$> interpret_tuple_term self' t' e
    | TVRecord t' => VRecord <$> interpret_record_term self' t' e
    | TVProjTuple t' i =>
        let* v := self' t' e in
        let* t := iv_monad_to_ivh_monad (unwrap_vtuple v) in
        match tuple_get i t with
        | None => throw (Invalid_argument "index out of bounds")
        | Some v' => pure v'
        end
    | TVProjRecord t' l =>
        let* v := self' t' e in
        let* r := iv_monad_to_ivh_monad (unwrap_vrecord v) in
        match record_lookup l r with
        | None => throw (Name_error (ident_car l))
        | Some v' => pure v'
        end
    | TVInl t' => VInl <$> self' t' e
    | TVInr t' => VInr <$> self' t' e
    | TVVariant l t' => VVariant l <$> self' t' e
    | TVRef t' =>
        let* v := self' t' e in
        state (fun h => (VRef (iheap_next_loc h), iheap_alloc v h))
    | TVArray t' =>
        let* '(n, vs) := interpret_array_term self' t' e in
        state (fun h => (VArray (iheap_next_loc h) (Z.of_nat n), array_of_list_alloc vs h))
    | TVGet t' =>
        let* v := self' t' e in
        let* l := iv_monad_to_ivh_monad (unwrap_vref v) in
        let* h := get in
        match iheap_read l h with
        | None => throw (Memory_error "ref_get")
        | Some v' => pure v'
        end
    | TVSet t1 t2 =>
        let* v1 := self' t1 e in
        let* v2 := self' t2 e in
        let* l := iv_monad_to_ivh_monad (unwrap_vref v1) in
        let* h := get in
        match iheap_write l v2 h with
        | None => throw (Memory_error "ref_set")
        | Some h' => VTt <$ put h'
        end
    | TVGetAt t1 t2 =>
        let* v1 := self' t1 e in
        let* v2 := self' t2 e in
        let* '(Array l z) := iv_monad_to_ivh_monad (unwrap_varray v1) in
        let* i := iv_monad_to_ivh_monad (unwrap_vint v2) in
        if (i <? 0) ||| (z <=? i) then
          throw (Invalid_argument "index out of bounds")
        else
          let* h := get in
          match iheap_read (loc_add l i) h with
          | None => throw (Memory_error "array_get_at")
          | Some v => pure v
          end
    | TVSetAt t1 t2 t3 =>
        let* v1 := self' t1 e in
        let* v2 := self' t2 e in
        let* v3 := self' t3 e in
        let* '(Array l z) := iv_monad_to_ivh_monad (unwrap_varray v1) in
        let* i := iv_monad_to_ivh_monad (unwrap_vint v2) in
        if (i <? 0) ||| (z <=? i) then
          throw (Invalid_argument "index out of bounds")
        else
          let* h := get in
          match iheap_write (loc_add l i) v3 h with
          | None => throw (Memory_error "array_set_at")
          | Some h' => VTt <$ put h'
          end
    | TVAssert t' =>
        let* v := self' t' e in
        let* b := iv_monad_to_ivh_monad (unwrap_vbool v) in
        if b then pure VTt else throw (Assert_failure "")
    | TVOp1 op t' =>
        let* v := self' t' e in
        iv_monad_to_ivh_monad (op.dispatch_op1 op v)
    | TVOp2 op t1 t2 =>
        let* v1 := self' t1 e in
        let* v2 := self' t2 e in
        iv_monad_to_ivh_monad (op.dispatch_op2 op v1 v2)
    | TVBuiltin1 l t' =>
        let* f := iv_monad_to_ivh_monad (builtin.dispatch_builtin1 l) in
        self' t' e >>= f
    | TVBuiltin2 l t1 t2 =>
        let* f := iv_monad_to_ivh_monad (builtin.dispatch_builtin2 l) in
        let* v := self' t1 e in
        self' t2 e >>= f v
    | TVBy t' => irh_monad_to_ivh_monad (self t' e KNil)
    end.

Definition interpret_val_term' (self : interpreter) (t : val_term) (e : env) : irh_monad val :=
  ivh_monad_to_irh_monad (interpret_val_term self t e).

Definition with_binder (b : binder) (v : val) (e : env) : env :=
  match b with
  | BAny => e
  | BVar x => ECons x v e
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

Fixpoint interpret_match_term (self : interpreter) (t : match_term) (e : env) (k : kont) (v : val) : irh_monad val :=
  match t with
  | TMatchNil => throw (IRRaise (Match_failure "interpret_match_term"))
  | TMatchCons p t1 t2 =>
      let* o := iv_monad_to_irh_monad (pattern.dispatch_pattern p v e) in
      match o with
      | Some e' => self t1 e' k
      | None => interpret_match_term self t2 e k v
      end
  end.

Fixpoint interpret_fix_mut_term (self : interpreter) (t : fix_mut_term) (e : env) (k : kont) (f : ident) (v : val) : irh_monad val :=
  match t with
  | TFixMutLast f' p t' =>
      if ident_eqb f f' then
        let* e' := iv_monad_to_irh_monad (pattern.dispatch_irrefutable_pattern p v e) in
        self t' e' k
      else throw (IRRaise (Name_error (ident_car f)))
  | TFixMutCons f' p t1 t2 =>
      if ident_eqb f f' then
        let* e' := iv_monad_to_irh_monad (pattern.dispatch_irrefutable_pattern p v e) in
        self t1 e' k
      else interpret_fix_mut_term self t2 e k f v
  end.

Definition interpret_ret_term (self : interpreter) (t : ret_term) (e : env) (k : kont) (v : val) : irh_monad val :=
  match t with
  | TRetNone => pure v
  | TRetSome p t' =>
      let* e' := iv_monad_to_irh_monad (pattern.dispatch_irrefutable_pattern p v e) in
      self t' e' k
  end.

Fixpoint interpret_exn_term (self : interpreter) (t : exn_term) (e : env) (k : kont) (v : val) : irh_monad val :=
  match t with
  | TExnLast p t' =>
      let* o := iv_monad_to_irh_monad (pattern.dispatch_pattern p v e) in
      match o with
      | Some e' => self t' e' k
      | None => throw (IRRaise v)
      end
  | TExnCons p t1 t2 =>
      let* o := iv_monad_to_irh_monad (pattern.dispatch_pattern p v e) in
      match o with
      | Some e' => self t1 e' k
      | None => interpret_exn_term self t2 e k v
      end
  end.

Fixpoint interpret_eff_term (self : interpreter) (t : eff_term) (e : env) (k : kont) (v : val) (u : val) (mk : metakont) : irh_monad val :=
  match t with
  | TEffLast p b t' =>
      let* o := iv_monad_to_irh_monad (pattern.dispatch_pattern p v e) in
      match o with
      | Some e' => self t' (with_binder b u e') k
      | None => throw (IRPerform mk v)
      end
  | TEffCons p b t1 t2 =>
      let* o := iv_monad_to_irh_monad (pattern.dispatch_pattern p v e) in
      match o with
      | Some e' => self t1 (with_binder b u e') k
      | None => interpret_eff_term self t2 e k v u mk
      end
  end.

Fixpoint unwind_reset (k : kont) (r : irequest) : irh_monad val :=
  match r with
  | IRShift mk f => catch (f (VMKReset mk)) (unwind_reset k)
  | IRControl mk f => throw (IRControl (MKReset mk k) f)
  | IRShift0 mk f => throw (IRShift0 (MKReset mk k) f)
  | IRControl0 mk f => throw (IRControl0 (MKReset mk k) f)
  | IRRaise _ => throw r
  | IRPerform mk v => throw (IRPerform (MKReset mk k) v)
  end.

Fixpoint unwind_prompt (k : kont) (r : irequest) : irh_monad val :=
  match r with
  | IRShift mk f => throw (IRShift (MKPrompt mk k) f)
  | IRControl mk f => catch (f (VMKPure mk)) (unwind_prompt k)
  | IRShift0 mk f => throw (IRShift0 (MKPrompt mk k) f)
  | IRControl0 mk f => throw (IRControl0 (MKPrompt mk k) f)
  | IRRaise _ => throw r
  | IRPerform mk v => throw (IRPerform (MKPrompt mk k) v)
  end.

Definition unwind_reset0 (k : kont) (r : irequest) : irh_monad val :=
  match r with
  | IRShift mk f => throw (IRShift (MKReset0 mk k) f)
  | IRControl mk f => throw (IRControl (MKReset0 mk k) f)
  | IRShift0 mk f => f (VMKReset0 mk) k
  | IRControl0 mk f => throw (IRControl0 (MKReset0 mk k) f)
  | IRRaise _ => throw r
  | IRPerform mk v => throw (IRPerform (MKReset0 mk k) v)
  end.

Definition unwind_prompt0 (k : kont) (r : irequest) : irh_monad val :=
  match r with
  | IRShift mk f => throw (IRShift (MKPrompt0 mk k) f)
  | IRControl mk f => throw (IRControl (MKPrompt0 mk k) f)
  | IRShift0 mk f => throw (IRShift0 (MKPrompt0 mk k) f)
  | IRControl0 mk f => f (VMKPure mk) k
  | IRRaise _ => throw r
  | IRPerform mk v => throw (IRPerform (MKPrompt0 mk k) v)
  end.

Definition unwind_try (self : interpreter) (t : exn_term) (e : env) (k : kont) (r : irequest) : irh_monad val :=
  match r with
  | IRShift mk f => throw (IRShift (MKTry mk t e k) f)
  | IRControl mk f => throw (IRControl (MKTry mk t e k) f)
  | IRShift0 mk f => throw (IRShift0 (MKTry mk t e k) f)
  | IRControl0 mk f => throw (IRControl0 (MKTry mk t e k) f)
  | IRRaise v => interpret_exn_term self t e k v
  | IRPerform mk v => throw (IRPerform (MKTry mk t e k) v)
  end.

Definition unwind_handle (self : interpreter) (t1 : ret_term) (t2 : eff_term) (e : env) (k : kont) (m : irequest + val) : irh_monad val :=
  match m with
  | inr v => interpret_ret_term self t1 e k v
  | inl r =>
      match r with
      | IRShift mk f => throw (IRShift (MKHandle mk t1 t2 e k) f)
      | IRControl mk f => throw (IRControl (MKHandle mk t1 t2 e k) f)
      | IRShift0 mk f => throw (IRShift0 (MKHandle mk t1 t2 e k) f)
      | IRControl0 mk f => throw (IRControl0 (MKHandle mk t1 t2 e k) f)
      | IRRaise _ => throw r
      | IRPerform mk v => interpret_eff_term self t2 e k v (VMKHandle mk t1 t2 e) (MKHandle mk t1 t2 e k)
      end
  end.

Definition unwind_shallow_handle (self : interpreter) (t1 : ret_term) (t2 : eff_term) (e : env) (k : kont) (m : irequest + val) : irh_monad val :=
  match m with
  | inr v => interpret_ret_term self t1 e k v
  | inl r =>
      match r with
      | IRShift mk f => throw (IRShift (MKShallowHandle mk t1 t2 e k) f)
      | IRControl mk f => throw (IRControl (MKShallowHandle mk t1 t2 e k) f)
      | IRShift0 mk f => throw (IRShift0 (MKShallowHandle mk t1 t2 e k) f)
      | IRControl0 mk f => throw (IRControl0 (MKShallowHandle mk t1 t2 e k) f)
      | IRRaise _ => throw r
      | IRPerform mk v => interpret_eff_term self t2 e k v (VMKPure mk) (MKShallowHandle mk t1 t2 e k)
      end
  end.

Fixpoint invoke_kont_app (self : interpreter) (k1 : kont) (k2 : kont) (v : val) : irh_monad val :=
  match k1 with
  | KNil => pure v
  | KCons0 t e k1' => self t e (KApp k1' k2) >>= invoke_kont_app self k1' k2
  | KCons1 p t e k1' =>
      let* e' := iv_monad_to_irh_monad (pattern.dispatch_irrefutable_pattern p v e) in
      self t e' (KApp k1' k2) >>= invoke_kont_app self k1' k2
  | KApp k11 k12 => invoke_kont_app self k11 (KApp k12 k2) v >>= invoke_kont_app self k12 k2
  end.

Fixpoint invoke_kont (self : interpreter) (k : kont) (v : val) : irh_monad val :=
  match k with
  | KNil => pure v
  | KCons0 t e k' => self t e k' >>= invoke_kont self k'
  | KCons1 p t e k' =>
      let* e' := iv_monad_to_irh_monad (pattern.dispatch_irrefutable_pattern p v e) in
      self t e' k' >>= invoke_kont self k'
  | KApp k1 k2 => invoke_kont_app self k1 k2 v >>= invoke_kont self k2
  end.

Fixpoint invoke_metakont (self : interpreter) (mk : metakont) (v : val) : irh_monad val :=
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

Definition invoke_metakont_app (self : interpreter) (mk : metakont) (k : kont) (v : val) : irh_monad val :=
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

Definition interpret_term'_aux (self : interpreter) : term -> env -> kont -> irh_monad val :=
  fix self' t e k :=
    match t with
    | TVal tv => interpret_val_term' self' tv e
    | TApp tv1 tv2 =>
        let* v1 := interpret_val_term' self' tv1 e in
        let* v2 := interpret_val_term' self' tv2 e in
        let* c := iv_monad_to_irh_monad (unwrap_vclosure v1) in
        match c with
        | CFun p t' e =>
            let* e' := iv_monad_to_irh_monad (pattern.dispatch_irrefutable_pattern p v2 e) in
            self t' e' k
        | CFix f p t' e =>
            let* e' := iv_monad_to_irh_monad (pattern.dispatch_irrefutable_pattern p v2 (ECons f v1 e)) in
            self t' e' k
        | CFixMut t' f e => interpret_fix_mut_term self t' (with_fix_mut_term t' e) k f v2
        | CMKPure mk => invoke_metakont_app self mk k v2
        | CMKReset mk => catch (invoke_metakont self mk v2) (unwind_reset k)
        | CMKReset0 mk => catch (invoke_metakont self mk v2) (unwind_reset0 k)
        | CMKHandle mk t1 t2 e => try (invoke_metakont self mk v2) >>= unwind_handle self t1 t2 e k
        end
    | TSeq t1 t2 =>
        let* _ := self' t1 e (KCons0 t2 e k) in
        self' t2 e k
    | TLet p t1 t2 =>
        let* v := self' t1 e (KCons1 p t2 e k) in
        let* e' := iv_monad_to_irh_monad (pattern.dispatch_irrefutable_pattern p v e) in
        self' t2 e' k
    | TMatch tv t' => interpret_val_term' self' tv e >>= interpret_match_term self' t' e k
    | TIf tv t1 t2 =>
        let* v := interpret_val_term' self' tv e in
        let* b := iv_monad_to_irh_monad (unwrap_vbool v) in
        if b then self' t1 e k else self' t2 e k
    | TWhile tv t' =>
        let* v := interpret_val_term' self' tv e in
        let* b := iv_monad_to_irh_monad (unwrap_vbool v) in
        if b then
          let* _ := self' t' e (KCons0 t e k) in
          self t e k
        else pure VTt
    | TFor b tv1 d tv2 t' =>
        let* v1 := interpret_val_term' self' tv1 e in
        let* v2 := interpret_val_term' self' tv2 e in
        let* i1 := iv_monad_to_irh_monad (unwrap_vint v1) in
        let* i2 := iv_monad_to_irh_monad (unwrap_vint v2) in
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
        in go (Z.to_nat (z + 1)) i1
    | TLetFix f p t1 t2 => self' t2 (ECons f (VFix f p t1 e) e) k
    | TLetFixMut t1 t2 => self' t2 (with_fix_mut_term t1 e) k
    | TShift b t' => throw (IRShift (MKPure k) (fun u => self' t' (with_binder b u e) KNil))
    | TControl b t' => throw (IRControl (MKPure k) (fun u => self' t' (with_binder b u e) KNil))
    | TShift0 b t' => throw (IRShift0 (MKPure k) (fun u => self' t' (with_binder b u e)))
    | TControl0 b t' => throw (IRControl0 (MKPure k) (fun u => self' t' (with_binder b u e)))
    | TReset t' => catch (self' t' e KNil) (unwind_reset k)
    | TPrompt t' => catch (self' t' e KNil) (unwind_prompt k)
    | TReset0 t' => catch (self' t' e KNil) (unwind_reset0 k)
    | TPrompt0 t' => catch (self' t' e KNil) (unwind_prompt0 k)
    | TRaise tv =>
        let* v := interpret_val_term' self' tv e in
        throw (IRRaise v)
    | TTry t1 t2 => catch (self' t1 e KNil) (unwind_try self' t2 e k)
    | TPerform tv =>
        let* v := interpret_val_term' self' tv e in
        throw (IRPerform (MKPure k) v)
    | THandle t1 t2 t3 => try (self' t1 e KNil) >>= unwind_handle self' t2 t3 e k
    | TShallowHandle t1 t2 t3 => try (self' t1 e KNil) >>= unwind_shallow_handle self' t2 t3 e k
    end.

Fixpoint interpret_term' (fuel : nat) (t : term) (e : env) (k : kont) : irh_monad val :=
  match fuel with
  | O => throw (IRRaise Out_of_fuel)
  | S fuel' => interpret_term'_aux (interpret_term' fuel') t e k
  end.

Definition interpret_term (fuel : nat) (t : term) (e : env) (k : kont) : ivh_monad val :=
  irh_monad_to_ivh_monad (interpret_term' fuel t e k).

Definition run_term (fuel : nat) (t : term) : (val + val) * iheap :=
  run_es_monad (interpret_term fuel t ENil KNil) iheap_empty.

Definition eval_term (fuel : nat) (t : term) : val + val :=
  fst (run_term fuel t).

Definition exec_term (fuel : nat) (t : term) : iheap :=
  snd (run_term fuel t).
