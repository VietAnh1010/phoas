From Stdlib Require Import Bool String ZArith.
From shift_reset.core Require Import syntax env fix_mut_defs ident loc record vals.
From shift_reset.monad Require Import es_monad.
From shift_reset.interpreter Require op prim.
From shift_reset.interpreter Require Import error iheap imonad pattern record unwrap.
Import ESMonadNotations.

Local Open Scope Z_scope.
Local Open Scope es_monad_scope.
Local Open Scope lazy_bool_scope.

Definition expr_interpreter : Type := expr -> env -> ivh_monad val.
Definition comp_interpreter : Type := comp -> env -> kont -> irh_monad val.
Definition isolated_comp_interpreter : Type := comp -> env -> ivh_monad val.
Definition prim_dispatcher : Type := ident -> val -> ivh_monad val.

Fixpoint interpret_exprs (interpret : expr_interpreter) (es : exprs) (rho : env) : ivh_monad vals :=
  match es with
  | EsNil => pure VsNil
  | EsCons e es' =>
      let* v := interpret e rho in
      VsCons v <$> interpret_exprs interpret es' rho
  end.

Definition interpret_record_expr (interpret : expr_interpreter) (e : record_expr) (rho : env) : ivh_monad record :=
  let fix go r e :=
    match e with
    | ERecordNil => pure r
    | ERecordRest e' =>
        let* v := interpret e' rho in
        let* r' := iv_monad_to_ivh_monad (unwrap_record v) in
        iv_monad_to_ivh_monad (extend_record r r')
    | ERecordCons l e1 e2 =>
        let* v := interpret e1 rho in
        let* r := iv_monad_to_ivh_monad (add_field l v r) in
        go r e2
    | ERecordConsPun l e' =>
        match env_find l rho with
        | None => throw (Name_error (ident_car l))
        | Some v =>
            let* r := iv_monad_to_ivh_monad (add_field l v r) in
            go r e'
        end
    end
  in go RecordNil e.

Definition interpret_get_at (v1 v2 : val) : ivh_monad val :=
  match v1 with
  | VArray l z =>
      let* i := iv_monad_to_ivh_monad (unwrap_int v2) in
      if (i <? 0) ||| (z <=? i) then
        throw (Invalid_argument "index out of bounds" v2)
      else
        let* h := get in
        match iheap_read (loc_add l i) h with
        | None => throw (Memory_error v1)
        | Some v => pure v
        end
  | VString s =>
      let* i := iv_monad_to_ivh_monad (unwrap_int v2) in
      if i <? 0 then
        throw (Invalid_argument "index out of bounds" v2)
      else
        match String.get (Z.to_nat i) s with
        | None => throw (Invalid_argument "index out of bounds" v2)
        | Some a => pure (VChar a)
        end
  | _ => throw (Type_error "array | string" v1)
  end.

Definition interpret_expr (interpret : isolated_comp_interpreter) : expr -> env -> ivh_monad val :=
  fix interpret' e rho :=
    match e with
    | EVar x =>
        match env_find x rho with
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
    | EAnd e1 e2 =>
        let* v := interpret' e1 rho in
        let* b := iv_monad_to_ivh_monad (unwrap_bool v) in
        if b then interpret' e2 rho else pure VFalse
    | EOr e1 e2 =>
        let* v := interpret' e1 rho in
        let* b := iv_monad_to_ivh_monad (unwrap_bool v) in
        if b then pure VTrue else interpret' e2 rho
    | EFun p c => pure (VFun p c rho)
    | EFix f p c => pure (VFix f p c rho)
    | EFixMut ds f => pure (VFixMut ds f rho)
    | EPair e1 e2 =>
        let* v := interpret' e1 rho in
        VPair v <$> interpret' e2 rho
    | ETuple es => VTuple <$> interpret_exprs interpret' es rho
    | ERecord e' => VRecord <$> interpret_record_expr interpret' e' rho
    | EFst e' =>
        let* v := interpret' e' rho in
        fst <$> iv_monad_to_ivh_monad (unwrap_prod v)
    | ESnd e' =>
        let* v := interpret' e' rho in
        snd <$> iv_monad_to_ivh_monad (unwrap_prod v)
    | EProjTuple e' n =>
        let* v := interpret' e' rho in
        let* '(Tuple vs) := iv_monad_to_ivh_monad (unwrap_tuple v) in
        match vals_get n vs with
        | None => throw (Invalid_argument "index out of bounds" (VInt (Z.of_nat n)))
        | Some v' => pure v'
        end
    | EProjRecord e' l =>
        let* v := interpret' e' rho in
        let* r := iv_monad_to_ivh_monad (unwrap_record v) in
        match record_find l r with
        | None => throw (Name_error (ident_car l))
        | Some v' => pure v'
        end
    | EUpdateRecord e1 e2 =>
        let* v := interpret' e1 rho in
        let* r2 := interpret_record_expr interpret' e2 rho in
        let* r1 := iv_monad_to_ivh_monad (unwrap_record v) in
        VRecord <$> iv_monad_to_ivh_monad (update_record r1 r2)
    | EInl e' => VInl <$> interpret' e' rho
    | EInr e' => VInr <$> interpret' e' rho
    | EVariant l e' => VVariant l <$> interpret' e' rho
    | EEnum l => pure (VEnum l)
    | ENil => pure VNil
    | ECons e1 e2 =>
        let* v := interpret' e1 rho in
        VCons v <$> interpret' e2 rho
    | ERef e' =>
        let* v := interpret' e' rho in
        VRef <$> state (iheap_alloc v)
    | EArray es =>
        let* vs := interpret_exprs interpret' es rho in
        let+ l := state (iheap_alloc_vals vs) in
        VArray l (Z.of_nat (vals_length vs))
    | EGet e' =>
        let* v := interpret' e' rho in
        let* l := iv_monad_to_ivh_monad (unwrap_ref v) in
        let* h := get in
        match iheap_read l h with
        | None => throw (Memory_error v)
        | Some v' => pure v'
        end
    | ESet e1 e2 =>
        let* v1 := interpret' e1 rho in
        let* v2 := interpret' e2 rho in
        let* l := iv_monad_to_ivh_monad (unwrap_ref v1) in
        let* h := get in
        match iheap_write l v2 h with
        | None => throw (Memory_error v1)
        | Some h => VTt <$ put h
        end
    | EGetAt e1 e2 =>
        let* v := interpret' e1 rho in
        interpret' e2 rho >>= interpret_get_at v
    | ESetAt e1 e2 e3 =>
        let* v1 := interpret' e1 rho in
        let* v2 := interpret' e2 rho in
        let* v3 := interpret' e3 rho in
        let* '(Array l z) := iv_monad_to_ivh_monad (unwrap_array v1) in
        let* i := iv_monad_to_ivh_monad (unwrap_int v2) in
        if (i <? 0) ||| (z <=? i) then
          throw (Invalid_argument "index out of bounds" v2)
        else
          let* h := get in
          match iheap_write (loc_add l i) v3 h with
          | None => throw (Memory_error v1)
          | Some h => VTt <$ put h
          end
    | EUnOp op e' =>
        let* v := interpret' e' rho in
        iv_monad_to_ivh_monad (op.dispatch_un_op op v)
    | EBinOp op e1 e2 =>
        let* v1 := interpret' e1 rho in
        let* v2 := interpret' e2 rho in
        iv_monad_to_ivh_monad (op.dispatch_bin_op op v1 v2)
    | EPrim l => pure (VPrim l)
    | EBy c => interpret c rho
    end.

Definition interpret_comp_isolated (interpret : comp_interpreter) (c : comp) (rho : env) : ivh_monad val :=
  irh_monad_to_ivh_monad (interpret c rho KNil).

Definition interpret_expr' (interpret : comp_interpreter) (e : expr) (rho : env) : irh_monad val :=
  ivh_monad_to_irh_monad (interpret_expr (interpret_comp_isolated interpret) e rho).

Definition with_binder (b : binder) (v : val) (rho : env) : env :=
  match b with
  | BAny => rho
  | BVar x => EnvCons x v rho
  end.

Definition with_fix_mut_defs (ds : fix_mut_defs) (rho : env) : env :=
  let fix go ds' rho' :=
    match ds' with
    | FixMutNil => rho'
    | FixMutCons f _ _ ds'' => go ds'' (EnvCons f (VFixMut ds f rho) rho')
    end
  in go ds rho.

Fixpoint interpret_match_cases (interpret : comp_interpreter) (cs : match_cases) (rho : env) (k : kont)
  (v : val) : irh_monad val :=
  match cs with
  | CasesNil => throw (IRRaise (Match_failure v))
  | CasesCons p c cs' =>
      match match_pattern p v rho with
      | None => interpret_match_cases interpret cs' rho k v
      | Some rho => interpret c rho k
      end
  end.

Fixpoint interpret_try_cases (interpret : comp_interpreter) (cs : try_cases) (rho : env) (k : kont)
  (v : val) : irh_monad val :=
  match cs with
  | CasesNil => throw (IRRaise v)
  | CasesCons p c cs' =>
      match match_pattern p v rho with
      | None => interpret_try_cases interpret cs' rho k v
      | Some rho => interpret c rho k
      end
  end.

Definition interpret_return_case (interpret : comp_interpreter) (c : return_case) (rho : env) (k : kont)
  (v : val) : irh_monad val :=
  match c with
  | ReturnCaseNone => pure v
  | ReturnCaseSome p c' =>
      let* rho := iv_monad_to_irh_monad (match_irrefutable_pattern p v rho) in
      interpret c' rho k
  end.

Fixpoint interpret_effect_cases (interpret : comp_interpreter) (cs : effect_cases) (rho : env) (k : kont)
  (v1 v2 : val) (mk : metakont) : irh_monad val :=
  match cs with
  | EffectCasesNil => throw (IRPerform mk v1)
  | EffectCasesCons p b c cs' =>
      match match_pattern p v1 rho with
      | None => interpret_effect_cases interpret cs' rho k v1 v2 mk
      | Some rho => interpret c (with_binder b v2 rho) k
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

Definition unwind_try (interpret : comp_interpreter) (cs : try_cases) (rho : env) (k : kont)
  (r : irequest) : irh_monad val :=
  match r with
  | IRShift mk f => throw (IRShift (MKTry mk cs rho k) f)
  | IRControl mk f => throw (IRControl (MKTry mk cs rho k) f)
  | IRRaise v => interpret_try_cases interpret cs rho k v
  | IRPerform mk v => throw (IRPerform (MKTry mk cs rho k) v)
  end.

Definition unwind_handle (interpret : comp_interpreter) (cs : handle_cases) (rho : env) (k : kont)
  (m : irequest + val) : irh_monad val :=
  let (c, cs') := cs in
  match m with
  | inr v => interpret_return_case interpret c rho k v
  | inl r =>
      match r with
      | IRShift mk f => throw (IRShift (MKHandle mk cs rho k) f)
      | IRControl mk f => throw (IRControl (MKHandle mk cs rho k) f)
      | IRRaise _ => throw r
      | IRPerform mk v => interpret_effect_cases interpret cs' rho k v (VMKHandle mk cs rho) (MKHandle mk cs rho k)
      end
  end.

Definition unwind_shallow_handle (interpret : comp_interpreter) (cs : handle_cases) (rho : env) (k : kont)
  (m : irequest + val) : irh_monad val :=
  let (c, cs') := cs in
  match m with
  | inr v => interpret_return_case interpret c rho k v
  | inl r =>
      match r with
      | IRShift mk f => throw (IRShift (MKShallowHandle mk cs rho k) f)
      | IRControl mk f => throw (IRControl (MKShallowHandle mk cs rho k) f)
      | IRRaise _ => throw r
      | IRPerform mk v => interpret_effect_cases interpret cs' rho k v (VMKPure mk) (MKShallowHandle mk cs rho k)
      end
  end.

Fixpoint invoke_kont_append (interpret : comp_interpreter) (k1 k2 : kont) (v : val) : irh_monad val :=
  match k1 with
  | KNil => pure v
  | KConsSeq c rho k1' => interpret c rho (KAppend k1' k2) >>= invoke_kont_append interpret k1' k2
  | KConsLet p c rho k1' =>
      let* rho := iv_monad_to_irh_monad (match_irrefutable_pattern p v rho) in
      interpret c rho (KAppend k1' k2) >>= invoke_kont_append interpret k1' k2
  | KAppend k11 k12 => invoke_kont_append interpret k11 (KAppend k12 k2) v >>= invoke_kont_append interpret k12 k2
  end.

Fixpoint invoke_kont (interpret : comp_interpreter) (k : kont) (v : val) : irh_monad val :=
  match k with
  | KNil => pure v
  | KConsSeq c rho k' => interpret c rho k' >>= invoke_kont interpret k'
  | KConsLet p c rho k' =>
      let* rho := iv_monad_to_irh_monad (match_irrefutable_pattern p v rho) in
      interpret c rho k' >>= invoke_kont interpret k'
  | KAppend k1 k2 => invoke_kont_append interpret k1 k2 v >>= invoke_kont interpret k2
  end.

Fixpoint invoke_metakont (interpret : comp_interpreter) (mk : metakont) (v : val) : irh_monad val :=
  match mk with
  | MKPure k => invoke_kont interpret k v
  | MKReset mk' k =>
      catch (invoke_metakont interpret mk' v) (unwind_reset k) >>= invoke_kont interpret k
  | MKPrompt mk' k =>
      catch (invoke_metakont interpret mk' v) (unwind_prompt k) >>= invoke_kont interpret k
  | MKTry mk' cs rho k =>
      catch (invoke_metakont interpret mk' v) (unwind_try interpret cs rho k) >>= invoke_kont interpret k
  | MKHandle mk' cs rho k =>
      let* m := try (invoke_metakont interpret mk' v) in
      unwind_handle interpret cs rho k m >>= invoke_kont interpret k
  | MKShallowHandle mk' cs rho k =>
      let* m := try (invoke_metakont interpret mk' v) in
      unwind_shallow_handle interpret cs rho k m >>= invoke_kont interpret k
  end.

Definition invoke_metakont_append (interpret : comp_interpreter) (mk : metakont) (k : kont) (v : val) : irh_monad val :=
  match mk with
  | MKPure k' => invoke_kont_append interpret k' k v
  | MKReset mk' k' =>
      catch (invoke_metakont interpret mk' v) (unwind_reset (KAppend k' k)) >>= invoke_kont_append interpret k' k
  | MKPrompt mk' k' =>
      catch (invoke_metakont interpret mk' v) (unwind_prompt (KAppend k' k)) >>= invoke_kont_append interpret k' k
  | MKTry mk' cs rho k' =>
      catch (invoke_metakont interpret mk' v) (unwind_try interpret cs rho (KAppend k' k)) >>= invoke_kont_append interpret k' k
  | MKHandle mk' cs rho k' =>
      let* m := try (invoke_metakont interpret mk' v) in
      unwind_handle interpret cs rho (KAppend k' k) m >>= invoke_kont_append interpret k' k
  | MKShallowHandle mk' cs rho k' =>
      let* m := try (invoke_metakont interpret mk' v) in
      unwind_shallow_handle interpret cs rho (KAppend k' k) m >>= invoke_kont_append interpret k' k
  end.

Definition interpret_for (interpret : comp_interpreter) (b : binder) (d : direction_flag) (c : comp) (rho : env) (k : kont)
  (v1 v2 : val) : irh_monad val :=
  let* i1 := iv_monad_to_irh_monad (unwrap_int v1) in
  let* i2 := iv_monad_to_irh_monad (unwrap_int v2) in
  let e := EInt i2 in
  let (f, z) :=
    match d with
    | Upto => (Z.succ, i2 - i1)
    | Downto => (Z.pred, i1 - i2)
    end
  in
  let fix go n i :=
    match n with
    | O => pure VTt
    | S n' =>
        let i' := f i in
        let* _ := interpret c (with_binder b (VInt i) rho) (KConsSeq (CFor b (EInt i') d e c) rho k) in
        go n' i'
    end
  in go (Z.to_nat (z + 1)) i1.

Definition apply (interpret : comp_interpreter) (dispatch : prim_dispatcher) (k : kont) (v1 v2 : val) : irh_monad val :=
  let* a := iv_monad_to_irh_monad (unwrap_applicable v1) in
  match a with
  | AFun p c rho =>
      let* rho := iv_monad_to_irh_monad (match_irrefutable_pattern p v2 rho) in
      interpret c rho k
  | AFix f p c rho =>
      let* rho := iv_monad_to_irh_monad (match_irrefutable_pattern p v2 (EnvCons f v1 rho)) in
      interpret c rho k
  | AFixMut ds f rho =>
      match fix_mut_defs_find_last f ds with
      | None => throw (IRRaise (Name_error (ident_car f)))
      | Some (p, c) =>
          let* rho := iv_monad_to_irh_monad (match_irrefutable_pattern p v2 (with_fix_mut_defs ds rho)) in
          interpret c rho k
      end
  | APrim l => ivh_monad_to_irh_monad (dispatch l v2)
  | AMKPure mk => invoke_metakont_append interpret mk k v2
  | AMKReset mk => catch (invoke_metakont interpret mk v2) (unwind_reset k)
  | AMKHandle mk cs rho => try (invoke_metakont interpret mk v2) >>= unwind_handle interpret cs rho k
  end.

Definition apply_isolated (interpret : comp_interpreter) (dispatch : prim_dispatcher) (v1 v2 : val) : ivh_monad val :=
  irh_monad_to_ivh_monad (apply interpret dispatch KNil v1 v2).

Definition interpret_comp'_aux (interpret : comp_interpreter) (dispatch : prim_dispatcher) : comp -> env -> kont -> irh_monad val :=
  fix interpret' c rho k :=
    match c with
    | CReturn e => interpret_expr' interpret' e rho
    | CApp e1 e2 =>
        let* v := interpret_expr' interpret' e1 rho in
        interpret_expr' interpret' e2 rho >>= apply interpret dispatch k v
    | CSeq c1 c2 =>
        let* _ := interpret' c1 rho (KConsSeq c2 rho k) in
        interpret' c2 rho k
    | CLet p c1 c2 =>
        let* v := interpret' c1 rho (KConsLet p c2 rho k) in
        let* rho := iv_monad_to_irh_monad (match_irrefutable_pattern p v rho) in
        interpret' c2 rho k
    | CMatch e cs => interpret_expr' interpret' e rho >>= interpret_match_cases interpret' cs rho k
    | CIf e c1 c2 =>
        let* v := interpret_expr' interpret' e rho in
        let* b := iv_monad_to_irh_monad (unwrap_bool v) in
        if b then interpret' c1 rho k else interpret' c2 rho k
    | CWhile e c' =>
        let* v := interpret_expr' interpret' e rho in
        let* b := iv_monad_to_irh_monad (unwrap_bool v) in
        if b then
          let* _ := interpret' c' rho (KConsSeq c rho k) in
          interpret c rho k
        else pure VTt
    | CFor b e1 d e2 c' =>
        let* v := interpret_expr' interpret' e1 rho in
        interpret_expr' interpret' e2 rho >>= interpret_for interpret' b d c' rho k v
    | CLetFun f p c1 c2 => interpret' c2 (EnvCons f (VFun p c1 rho) rho) k
    | CLetFix f p c1 c2 => interpret' c2 (EnvCons f (VFix f p c1 rho) rho) k
    | CLetFixMut ds c' => interpret' c' (with_fix_mut_defs ds rho) k
    | CShift b c' => throw (IRShift (MKPure k) (fun v => interpret' c' (with_binder b v rho) KNil))
    | CControl b c' => throw (IRControl (MKPure k) (fun v => interpret' c' (with_binder b v rho) KNil))
    | CReset c' => catch (interpret' c' rho KNil) (unwind_reset k)
    | CPrompt c' => catch (interpret' c' rho KNil) (unwind_prompt k)
    | CRaise e =>
        let* v := interpret_expr' interpret' e rho in
        throw (IRRaise v)
    | CPerform e =>
        let* v := interpret_expr' interpret' e rho in
        throw (IRPerform (MKPure k) v)
    | CTry c' cs => catch (interpret' c' rho KNil) (unwind_try interpret' cs rho k)
    | CHandle c' cs => try (interpret' c' rho KNil) >>= unwind_handle interpret' cs rho k
    | CShallowHandle c' cs => try (interpret' c' rho KNil) >>= unwind_shallow_handle interpret' cs rho k
    end.

Fixpoint interpret_comp' (fuel : nat) (c : comp) (rho : env) (k : kont) : irh_monad val :=
  match fuel with
  | O => throw (IRRaise Out_of_fuel)
  | S fuel' => interpret_comp'_aux (interpret_comp' fuel') (dispatch_prim fuel') c rho k
  end
with dispatch_prim (fuel : nat) (l : ident) (v : val) : ivh_monad val :=
  match fuel with
  | O => throw Out_of_fuel
  | S fuel' => prim.dispatch_prim_aux (apply_isolated (interpret_comp' fuel') (dispatch_prim fuel')) l v
  end.

Definition interpret_comp (fuel : nat) (c : comp) (rho : env) (k : kont) : ivh_monad val :=
  irh_monad_to_ivh_monad (interpret_comp' fuel c rho k).

Definition run_comp (fuel : nat) (c : comp) : (val + val) * iheap :=
  run_es_monad (interpret_comp fuel c EnvNil KNil) iheap_empty.

Definition eval_comp (fuel : nat) (c : comp) : val + val :=
  fst (run_comp fuel c).

Definition exec_comp (fuel : nat) (c : comp) : iheap :=
  snd (run_comp fuel c).
