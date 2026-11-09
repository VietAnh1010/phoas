From Stdlib Require Import Bool List String ZArith.
From shift_reset.core Require Import syntax env ident loc record tuple.
From shift_reset.monad Require Import es_monad.
From shift_reset.interpreter Require op prim.
From shift_reset.interpreter Require Import array error iheap imonad pattern unwrap.
Import ESMonadNotations ListNotations.

Local Open Scope Z_scope.
Local Open Scope es_monad_scope.
Local Open Scope lazy_bool_scope.

Definition val_interpreter : Type := expr -> env -> ivh_monad val.
Definition interpreter : Type := comp -> env -> kont -> irh_monad val.

Fixpoint interpret_tuple_expr (self : val_interpreter) (t : tuple_expr) (e : env) : ivh_monad tuple :=
  match t with
  | ETupleNil => pure TupleNil
  | ETupleCons t1 t2 =>
      let* v := self t1 e in
      TupleCons v <$> interpret_tuple_expr self t2 e
  end.

Fixpoint interpret_record_expr (self : val_interpreter) (t : record_expr) (e : env) : ivh_monad record :=
  match t with
  | ERecordNil => pure RecordNil
  | ERecordRest t' =>
      let* v := self t' e in
      iv_monad_to_ivh_monad (unwrap_vrecord v)
  | ERecordConsPun l t' =>
      match env_find l e with
      | None => throw (Name_error (ident_car l))
      | Some v => RecordCons l v <$> interpret_record_expr self t' e
      end
  | ERecordCons l t1 t2 =>
      let* v := self t1 e in
      RecordCons l v <$> interpret_record_expr self t2 e
  end.

Definition interpret_variant_expr (self : val_interpreter) (t : variant_expr) (e : env) : ivh_monad variant :=
  match t with
  | EVariantNone l => pure (VariantNone l)
  | EVariantSome l t' => VariantSome l <$> self t' e
  end.

Fixpoint update_record (r1 r2 : record) : ivh_monad record :=
  match r2 with
  | RecordNil => pure r1
  | RecordCons l v r2' =>
      match record_replace l v r1 with
      | None => throw (Name_error (ident_car l))
      | Some r1' => update_record r1' r2'
      end
  end.

Fixpoint interpret_array_expr (self : val_interpreter) (t : array_expr) (e : env) : ivh_monad (nat * list val) :=
  match t with
  | EArrayNil => pure (O, [])
  | EArrayCons t1 t2 =>
      let* v := self t1 e in
      let+ '(n, vs) := interpret_array_expr self t2 e in
      (S n, v :: vs)
  end.

Definition interpret_expr (self : interpreter) : expr -> env -> ivh_monad val :=
  fix self' t e :=
    match t with
    | EVar x =>
        match env_find x e with
        | None => throw (Name_error (ident_car x))
        | Some v => pure v
        end
    | ETt => pure VTt
    | EInt z => pure (VInt z)
    | EFloat q => pure (VFloat q)
    | ETrue => pure VTrue
    | EFalse => pure VFalse
    | EChar a => pure (VChar a)
    | EString s => pure (VString s)
    | EAnd t1 t2 =>
        let* v := self' t1 e in
        let* b := iv_monad_to_ivh_monad (unwrap_vbool v) in
        if b then self' t2 e else pure VFalse
    | EOr t1 t2 =>
        let* v := self' t1 e in
        let* b := iv_monad_to_ivh_monad (unwrap_vbool v) in
        if b then pure VTrue else self' t2 e
    | EFun p t' => pure (VFun p t' e)
    | EFix f p t' => pure (VFix f p t' e)
    | EFixMut t' f => pure (VFixMut t' f e)
    | EPair t1 t2 =>
        let* v := self' t1 e in
        VPair v <$> self' t2 e
    | EFst t' =>
        let* v := self' t' e in
        fst <$> iv_monad_to_ivh_monad (unwrap_vprod v)
    | ESnd t' =>
        let* v := self' t' e in
        snd <$> iv_monad_to_ivh_monad (unwrap_vprod v)
    | ETuple t' => VTuple <$> interpret_tuple_expr self' t' e
    | ERecord t' => VRecord <$> interpret_record_expr self' t' e
    | EProjTuple t' i =>
        let* v := self' t' e in
        let* t := iv_monad_to_ivh_monad (unwrap_vtuple v) in
        match tuple_get i t with
        | None => throw (Invalid_argument "index out of bounds")
        | Some v' => pure v'
        end
    | EProjRecord t' l =>
        let* v := self' t' e in
        let* r := iv_monad_to_ivh_monad (unwrap_vrecord v) in
        match record_find l r with
        | None => throw (Name_error (ident_car l))
        | Some v' => pure v'
        end
    | EUpdateRecord t1 t2 =>
        let* v := self' t1 e in
        let* r1 := iv_monad_to_ivh_monad (unwrap_vrecord v) in
        let* r2 := interpret_record_expr self' t2 e in
        VRecord <$> update_record r1 r2
    | EInl t' => VInl <$> self' t' e
    | EInr t' => VInr <$> self' t' e
    | ENil => pure VNil
    | ECons t1 t2 =>
        let* v := self' t1 e in
        VCons v <$> self' t2 e
    | EVariant t' => VVariant <$> interpret_variant_expr self' t' e
    | ERef t' =>
        let* v := self' t' e in
        state (fun h => (VRef (iheap_next_loc h), iheap_alloc v h))
    | EArray t' =>
        let* '(n, vs) := interpret_array_expr self' t' e in
        state (fun h => (VArray (iheap_next_loc h) (Z.of_nat n), array_of_list_alloc vs h))
    | EGet t' =>
        let* v := self' t' e in
        let* l := iv_monad_to_ivh_monad (unwrap_vref v) in
        let* h := get in
        match iheap_read l h with
        | None => throw (Memory_error "ref_get")
        | Some v' => pure v'
        end
    | ESet t1 t2 =>
        let* v1 := self' t1 e in
        let* v2 := self' t2 e in
        let* l := iv_monad_to_ivh_monad (unwrap_vref v1) in
        let* h := get in
        match iheap_write l v2 h with
        | None => throw (Memory_error "ref_set")
        | Some h' => VTt <$ put h'
        end
    | EGetAt t1 t2 =>
        let* v1 := self' t1 e in
        let* v2 := self' t2 e in
        match v1 with
        | VArray l z =>
            let* i := iv_monad_to_ivh_monad (unwrap_vint v2) in
            if (i <? 0) ||| (z <=? i) then
              throw (Invalid_argument "index out of bounds")
            else
              let* h := get in
              match iheap_read (loc_add l i) h with
              | None => throw (Memory_error "array_get_at")
              | Some v => pure v
              end
        | VString s =>
            let* i := iv_monad_to_ivh_monad (unwrap_vint v2) in
            if i <? 0 then
              throw (Invalid_argument "index out of bounds")
            else
              match String.get (Z.to_nat i) s with
              | None => throw (Invalid_argument "index out of bounds")
              | Some a => pure (VChar a)
              end
        | _ => throw (Type_error "array | string" v1)
        end
    | ESetAt t1 t2 t3 =>
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
    | EOp1 op t' =>
        let* v := self' t' e in
        iv_monad_to_ivh_monad (op.dispatch_op1 op v)
    | EOp2 op t1 t2 =>
        let* v1 := self' t1 e in
        let* v2 := self' t2 e in
        iv_monad_to_ivh_monad (op.dispatch_op2 op v1 v2)
    | EPrim l => pure (VPrim l)
    | EBy t' => irh_monad_to_ivh_monad (self t' e KNil)
    end.

Definition interpret_expr' (self : interpreter) (t : expr) (e : env) : irh_monad val :=
  ivh_monad_to_irh_monad (interpret_expr self t e).

Definition with_binder (b : binder) (v : val) (e : env) : env :=
  match b with
  | BAny => e
  | BVar x => EnvCons x v e
  end.

Definition with_for_direction (d : for_direction) (i1 i2 : Z) : (Z -> Z) * Z :=
  match d with
  | Upto => (Z.succ, i2 - i1)
  | Downto => (Z.pred, i1 - i2)
  end.

Fixpoint with_fix_mut_term (t : fix_mut_term) (e : env) : env :=
  match t with
  | TFixMutLast f _ _ => EnvCons f (VFixMut t f e) e
  | TFixMutCons f _ _ t' => with_fix_mut_term t' (EnvCons f (VFixMut t f e) e)
  end.

Fixpoint interpret_match_term (self : interpreter) (t : match_term) (e : env) (k : kont) (v : val) : irh_monad val :=
  match t with
  | TMatchNil => throw (IRRaise (Match_failure "interpret_match_term"))
  | TMatchCons p t1 t2 =>
      let* o := iv_monad_to_irh_monad (match_pattern p v e) in
      match o with
      | Some e' => self t1 e' k
      | None => interpret_match_term self t2 e k v
      end
  end.

Fixpoint interpret_fix_mut_term (self : interpreter) (t : fix_mut_term) (e : env) (k : kont) (f : ident) (v : val) : irh_monad val :=
  match t with
  | TFixMutLast f' p t' =>
      if ident_eqb f f' then
        let* e' := iv_monad_to_irh_monad (match_irrefutable_pattern p v e) in
        self t' e' k
      else throw (IRRaise (Name_error (ident_car f)))
  | TFixMutCons f' p t1 t2 =>
      if ident_eqb f f' then
        let* e' := iv_monad_to_irh_monad (match_irrefutable_pattern p v e) in
        self t1 e' k
      else interpret_fix_mut_term self t2 e k f v
  end.

Definition interpret_ret_term (self : interpreter) (t : ret_term) (e : env) (k : kont) (v : val) : irh_monad val :=
  match t with
  | TRetNone => pure v
  | TRetSome p t' =>
      let* e' := iv_monad_to_irh_monad (match_irrefutable_pattern p v e) in
      self t' e' k
  end.

Fixpoint interpret_exn_term (self : interpreter) (t : exn_term) (e : env) (k : kont) (v : val) : irh_monad val :=
  match t with
  | TExnLast p t' =>
      let* o := iv_monad_to_irh_monad (match_pattern p v e) in
      match o with
      | Some e' => self t' e' k
      | None => throw (IRRaise v)
      end
  | TExnCons p t1 t2 =>
      let* o := iv_monad_to_irh_monad (match_pattern p v e) in
      match o with
      | Some e' => self t1 e' k
      | None => interpret_exn_term self t2 e k v
      end
  end.

Fixpoint interpret_eff_term (self : interpreter) (t : eff_term) (e : env) (k : kont) (v : val) (u : val) (mk : metakont) : irh_monad val :=
  match t with
  | TEffLast p b t' =>
      let* o := iv_monad_to_irh_monad (match_pattern p v e) in
      match o with
      | Some e' => self t' (with_binder b u e') k
      | None => throw (IRPerform mk v)
      end
  | TEffCons p b t1 t2 =>
      let* o := iv_monad_to_irh_monad (match_pattern p v e) in
      match o with
      | Some e' => self t1 (with_binder b u e') k
      | None => interpret_eff_term self t2 e k v u mk
      end
  end.

Fixpoint unwind_reset (k : kont) (r : irequest) : irh_monad val :=
  match r with
  | IRShift mk f => catch (f (VMKReset mk)) (unwind_reset k)
  | IRControl mk f => throw (IRControl (MKReset mk k) f)
  | IRRaise _ => throw r
  | IRPerform mk v => throw (IRPerform (MKReset mk k) v)
  end.

Fixpoint unwind_prompt (k : kont) (r : irequest) : irh_monad val :=
  match r with
  | IRShift mk f => throw (IRShift (MKPrompt mk k) f)
  | IRControl mk f => catch (f (VMKPure mk)) (unwind_prompt k)
  | IRRaise _ => throw r
  | IRPerform mk v => throw (IRPerform (MKPrompt mk k) v)
  end.

Definition unwind_try (self : interpreter) (t : exn_term) (e : env) (k : kont) (r : irequest) : irh_monad val :=
  match r with
  | IRShift mk f => throw (IRShift (MKTry mk t e k) f)
  | IRControl mk f => throw (IRControl (MKTry mk t e k) f)
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
      | IRRaise _ => throw r
      | IRPerform mk v => interpret_eff_term self t2 e k v (VMKPure mk) (MKShallowHandle mk t1 t2 e k)
      end
  end.

Fixpoint invoke_kont_app (self : interpreter) (k1 : kont) (k2 : kont) (v : val) : irh_monad val :=
  match k1 with
  | KNil => pure v
  | KConsSeq t e k1' => self t e (KApp k1' k2) >>= invoke_kont_app self k1' k2
  | KConsLet p t e k1' =>
      let* e' := iv_monad_to_irh_monad (match_irrefutable_pattern p v e) in
      self t e' (KApp k1' k2) >>= invoke_kont_app self k1' k2
  | KApp k11 k12 => invoke_kont_app self k11 (KApp k12 k2) v >>= invoke_kont_app self k12 k2
  end.

Fixpoint invoke_kont (self : interpreter) (k : kont) (v : val) : irh_monad val :=
  match k with
  | KNil => pure v
  | KConsSeq t e k' => self t e k' >>= invoke_kont self k'
  | KConsLet p t e k' =>
      let* e' := iv_monad_to_irh_monad (match_irrefutable_pattern p v e) in
      self t e' k' >>= invoke_kont self k'
  | KApp k1 k2 => invoke_kont_app self k1 k2 v >>= invoke_kont self k2
  end.

Fixpoint invoke_metakont (self : interpreter) (mk : metakont) (v : val) : irh_monad val :=
  match mk with
  | MKPure k => invoke_kont self k v
  | MKReset mk' k => catch (invoke_metakont self mk' v) (unwind_reset k) >>= invoke_kont self k
  | MKPrompt mk' k => catch (invoke_metakont self mk' v) (unwind_prompt k) >>= invoke_kont self k
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
  | MKTry mk' t e k' => catch (invoke_metakont self mk' v) (unwind_try self t e (KApp k' k)) >>= invoke_kont_app self k' k
  | MKHandle mk' t1 t2 e k' =>
      let* m := try (invoke_metakont self mk' v) in
      unwind_handle self t1 t2 e (KApp k' k) m >>= invoke_kont_app self k' k
  | MKShallowHandle mk' t1 t2 e k' =>
      let* m := try (invoke_metakont self mk' v) in
      unwind_shallow_handle self t1 t2 e (KApp k' k) m >>= invoke_kont_app self k' k
  end.

Definition interpret_comp'_aux (self : interpreter) : comp -> env -> kont -> irh_monad val :=
  fix self' t e k :=
    match t with
    | TVal tv => interpret_expr' self' tv e
    | CApp tv1 tv2 =>
        let* v1 := interpret_expr' self' tv1 e in
        let* v2 := interpret_expr' self' tv2 e in
        let* a := iv_monad_to_irh_monad (unwrap_vapplicable v1) in
        match a with
        | AFun p t' e =>
            let* e' := iv_monad_to_irh_monad (match_irrefutable_pattern p v2 e) in
            self t' e' k
        | AFix f p t' e =>
            let* e' := iv_monad_to_irh_monad (match_irrefutable_pattern p v2 (EnvCons f v1 e)) in
            self t' e' k
        | AFixMut t' f e => interpret_fix_mut_term self t' (with_fix_mut_term t' e) k f v2
        | APrim l =>
            let* f := iv_monad_to_irh_monad (prim.dispatch_prim l) in
            ivh_monad_to_irh_monad (f v2)
        | AMKPure mk => invoke_metakont_app self mk k v2
        | AMKReset mk => catch (invoke_metakont self mk v2) (unwind_reset k)
        | AMKHandle mk t1 t2 e => try (invoke_metakont self mk v2) >>= unwind_handle self t1 t2 e k
        end
    | CSeq t1 t2 =>
        let* _ := self' t1 e (KConsSeq t2 e k) in
        self' t2 e k
    | CLet p t1 t2 =>
        let* v := self' t1 e (KConsLet p t2 e k) in
        let* e' := iv_monad_to_irh_monad (match_irrefutable_pattern p v e) in
        self' t2 e' k
    | CMatch tv t' => interpret_expr' self' tv e >>= interpret_match_term self' t' e k
    | CIf tv t1 t2 =>
        let* v := interpret_expr' self' tv e in
        let* b := iv_monad_to_irh_monad (unwrap_vbool v) in
        if b then self' t1 e k else self' t2 e k
    | CWhile tv t' =>
        let* v := interpret_expr' self' tv e in
        let* b := iv_monad_to_irh_monad (unwrap_vbool v) in
        if b then
          let* _ := self' t' e (KConsSeq t e k) in
          self t e k
        else pure VTt
    | CFor b tv1 d tv2 t' =>
        let* v1 := interpret_expr' self' tv1 e in
        let* v2 := interpret_expr' self' tv2 e in
        let* i1 := iv_monad_to_irh_monad (unwrap_vint v1) in
        let* i2 := iv_monad_to_irh_monad (unwrap_vint v2) in
        let tv := EInt i2 in
        let (f, z) := with_for_direction d i1 i2 in
        let fix go n i :=
          match n with
          | O => pure VTt
          | S n' =>
              let i' := f i in
              let* _ := self' t' (with_binder b (VInt i) e) (KConsSeq (CFor b (EInt i') d tv t') e k) in
              go n' i'
          end
        in go (Z.to_nat (z + 1)) i1
    | CLetFix f p t1 t2 => self' t2 (EnvCons f (VFix f p t1 e) e) k
    | CLetFixMut t1 t2 => self' t2 (with_fix_mut_term t1 e) k
    | CShift b t' => throw (IRShift (MKPure k) (fun u => self' t' (with_binder b u e) KNil))
    | CControl b t' => throw (IRControl (MKPure k) (fun u => self' t' (with_binder b u e) KNil))
    | CReset t' => catch (self' t' e KNil) (unwind_reset k)
    | CPrompt t' => catch (self' t' e KNil) (unwind_prompt k)
    | CRaise tv =>
        let* v := interpret_expr' self' tv e in
        throw (IRRaise v)
    | CTry t1 t2 => catch (self' t1 e KNil) (unwind_try self' t2 e k)
    | CPerform tv =>
        let* v := interpret_expr' self' tv e in
        throw (IRPerform (MKPure k) v)
    | CHandle t1 t2 t3 => try (self' t1 e KNil) >>= unwind_handle self' t2 t3 e k
    | CShallowHandle t1 t2 t3 => try (self' t1 e KNil) >>= unwind_shallow_handle self' t2 t3 e k
    end.

Fixpoint interpret_comp' (fuel : nat) (t : comp) (e : env) (k : kont) : irh_monad val :=
  match fuel with
  | O => throw (IRRaise Out_of_fuel)
  | S fuel' => interpret_comp'_aux (interpret_comp' fuel') t e k
  end.

Definition interpret_comp (fuel : nat) (t : comp) (e : env) (k : kont) : ivh_monad val :=
  irh_monad_to_ivh_monad (interpret_comp' fuel t e k).

Definition run_comp (fuel : nat) (t : comp) : (val + val) * iheap :=
  run_es_monad (interpret_comp fuel t EnvNil KNil) iheap_empty.

Definition eval_comp (fuel : nat) (t : comp) : val + val :=
  fst (run_comp fuel t).

Definition exec_comp (fuel : nat) (t : comp) : iheap :=
  snd (run_comp fuel t).
