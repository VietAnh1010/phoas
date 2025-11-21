From Stdlib Require Import String Qcanon ZArith.
From shift_reset.core Require Import syntax env loc record tag var.
From shift_reset.interpreter Require Import builtin ierror iheap imonad op unwrap.

Local Open Scope string_scope.
Local Open Scope imonad_scope.
Local Unset Elimination Schemes.

Fixpoint interpret_val_term (t : val_term) : imonad val :=
  match t with
  | TVVar x =>
      e <- imonad_ask_env;
      match env_lookup x e with
      | None => imonad_throw_error (Name_error (var_car x))
      | Some v => imonad_pure v
      end
  | TVTt => imonad_pure VTt
  | TVInt z => imonad_pure (VInt z)
  | TVFloat q => imonad_pure (VFloat q)
  | TVTrue => imonad_pure VTrue
  | TVFalse => imonad_pure VFalse
  | TVChar a => imonad_pure (VChar a)
  | TVString s => imonad_pure (VString s)
  | TVAnd t1 t2 =>
      v <- interpret_val_term t1;
      b <- unwrap_vbool v;
      if b then interpret_val_term t2 else imonad_pure VFalse
  | TVOr t1 t2 =>
      v <- interpret_val_term t1;
      b <- unwrap_vbool v;
      if b then imonad_pure VTrue else interpret_val_term t2
  | TVFun b t' => imonad_asks_env (VFun b t')
  | TVFix f b t' => imonad_asks_env (VFix f b t')
  | TVFixMut t' f => imonad_asks_env (VFixMut t' f)
  | TVPair t1 t2 =>
      v <- interpret_val_term t1;
      VPair v <$> interpret_val_term t2
  | TVFst t' =>
      v <- interpret_val_term t';
      fst <$> unwrap_vprod v
  | TVSnd t' =>
      v <- interpret_val_term t';
      snd <$> unwrap_vprod v
  | TVTuple t' => VTuple <$> interpret_tuple_term t'
  | TVRecord t' => VRecord <$> interpret_record_term t'
  | TVProj t' tag =>
      v <- interpret_val_term t';
      r <- unwrap_vrecord v;
      match record_lookup tag r with
      | None => imonad_throw_error (Name_error (tag_car tag))
      | Some v' => imonad_pure v'
      end
  | TVInl t' => VInl <$> interpret_val_term t'
  | TVInr t' => VInr <$> interpret_val_term t'
  | TVVariant tag t' => VVariant tag <$> interpret_val_term t'
  | TVRef t' =>
      v <- interpret_val_term t';
      h <- imonad_get_heap;
      match iheap_ref v h with
      | None => imonad_throw_error (Memory_error "ref")
      | Some (l, h') => VRef l <$ imonad_set_heap h'
      end
  | TVGet t' =>
      v <- interpret_val_term t';
      l <- unwrap_vref v;
      h <- imonad_get_heap;
      match iheap_get l h with
      | None => imonad_throw_error (Memory_error "get")
      | Some v' => imonad_pure v'
      end
  | TVSet t1 t2 =>
      v <- interpret_val_term t1;
      l <- unwrap_vref v;
      v <- interpret_val_term t2;
      h <- imonad_get_heap;
      match iheap_set l v h with
      | None => imonad_throw_error (Memory_error "set")
      | Some h' => VTt <$ imonad_set_heap h'
      end
  | TVFree t' =>
      v <- interpret_val_term t';
      l <- unwrap_vref v;
      h <- imonad_get_heap;
      match iheap_free l h with
      | None => imonad_throw_error (Memory_error "free")
      | Some h' => VTt <$ imonad_set_heap h'
      end
  | TVExn tag t' => VExn tag <$> interpret_val_term t'
  | TVEff tag t' => VEff tag <$> interpret_val_term t'
  | TVAssert t' =>
      v <- interpret_val_term t';
      b <- unwrap_vbool v;
      if b then imonad_pure VTt else imonad_throw_error (Assert_failure "")
  | TVOp1 op t' => interpret_val_term t' >>= dispatch_op1 op
  | TVOp2 op t1 t2 =>
      v <- interpret_val_term t1;
      f <- dispatch_op2 op v;
      interpret_val_term t2 >>= f
  | TVBuiltin tag t' =>
      f <- dispatch_builtin tag;
      interpret_val_term t' >>= f
  end
with interpret_tuple_term (t : tuple_term) : imonad tuple :=
  match t with
  | TTupleNil => imonad_pure TupleNil
  | TTupleCons t1 t2 =>
      v <- interpret_val_term t1;
      TupleCons v <$> interpret_tuple_term t2
  end
with interpret_record_term (t : record_term) : imonad record :=
  match t with
  | TRecordNil => imonad_pure RecordNil
  | TRecordCons tag t1 t2 =>
      v <- interpret_val_term t1;
      RecordCons tag v <$> interpret_record_term t2
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

Definition with_fix_mut_term (t : fix_mut_term) (e : env) : env :=
  (fix go (t' : fix_mut_term) (e' : env) : env :=
     match t' with
     | TFixMutLast f _ _ => ECons f (VFixMut t f e) e'
     | TFixMutCons f _ _ t'' => go t'' (ECons f (VFixMut t f e) e')
     end) t e.

Inductive iresult : Type :=
| IRVal : val -> iresult
| IRShift : metakont -> (val -> imonad iresult) -> iresult
| IRControl : metakont -> (val -> imonad iresult) -> iresult
| IRRaise : tag -> val -> iresult
| IRPerform : metakont -> tag -> val -> iresult.

Definition IRPerform' (mk : metakont) (e : eff) : iresult :=
  let (tag, v) := e in IRPerform mk tag v.

Definition IRRaise' (e : exn) : iresult :=
  let (tag, v) := e in IRRaise tag v.

Record ikont : Type := IKont { ikont_car :> kont; ikont_app : val -> imonad iresult }.

Definition ikont_nil : ikont := IKont KNil (fun v => imonad_pure (IRVal v)).

Definition interpreter : Type := term -> ikont -> imonad iresult.

Definition interpret_ret_term_under (e : env) (self : interpreter) (t : ret_term) (k : ikont) (v : val) : imonad iresult :=
  match t with
  | TRetNone => ikont_app k v
  | TRetSome b t' => imonad_under_env (with_binder b v e) (self t' k)
  end.

Fixpoint interpret_exn_term_under (e : env) (self : interpreter) (t : exn_term) (k : ikont) (tag : tag) (v : val) : option (imonad iresult) :=
  match t with
  | TExnLast p t' =>
      match match_exn p tag v e with
      | Some e' => Some (imonad_under_env e' (self t' k))
      | None => None
      end
  | TExnCons p t1 t2 =>
      match match_exn p tag v e with
      | Some e' => Some (imonad_under_env e' (self t1 k))
      | None => interpret_exn_term_under e self t2 k tag v
      end
  end.

Fixpoint interpret_eff_term_under (e : env) (self : interpreter) (t : eff_term) (k : ikont) (tag : tag) (v u : val) : option (imonad iresult) :=
  match t with
  | TEffLast p b t' =>
      match match_eff p tag v e with
      | Some e' => Some (imonad_under_env (with_binder b u e') (self t' k))
      | None => None
      end
  | TEffCons p b t1 t2 =>
      match match_eff p tag v e with
      | Some e' => Some (imonad_under_env (with_binder b u e') (self t1 k))
      | None => interpret_eff_term_under e self t2 k tag v u
      end
  end.

Fixpoint unwind_reset (k : ikont) (r : iresult) : imonad iresult :=
  match r with
  | IRVal v => ikont_app k v
  | IRShift mk f => f (VMKReset mk) >>= unwind_reset k
  | IRControl mk f => imonad_pure (IRControl (MKReset mk k) f)
  | IRRaise _ _ => imonad_pure r
  | IRPerform mk tag v => imonad_pure (IRPerform (MKReset mk k) tag v)
  end.

Fixpoint unwind_prompt (k : ikont) (r : iresult) : imonad iresult :=
  match r with
  | IRVal v => ikont_app k v
  | IRShift mk f => imonad_pure (IRShift (MKPrompt mk k) f)
  | IRControl mk f => f (VMKPure mk) >>= unwind_prompt k
  | IRRaise _ _ => imonad_pure r
  | IRPerform mk tag v => imonad_pure (IRPerform (MKPrompt mk k) tag v)
  end.

Definition unwind_try (e : env) (self : interpreter) (t : exn_term) (k : ikont) (r : iresult) : imonad iresult :=
  match r with
  | IRVal v => ikont_app k v
  | IRShift mk f => imonad_pure (IRShift (MKTry mk t e k) f)
  | IRControl mk f => imonad_pure (IRControl (MKTry mk t e k) f)
  | IRRaise tag v =>
      match interpret_exn_term_under e self t k tag v with
      | Some m => m
      | None => imonad_pure r
      end
  | IRPerform mk tag v => imonad_pure (IRPerform (MKTry mk t e k) tag v)
  end.

Definition unwind_handle (e : env) (self : interpreter) (t1 : ret_term) (t2 : eff_term) (k : ikont) (r : iresult) : imonad iresult :=
  match r with
  | IRVal v => interpret_ret_term_under e self t1 k v
  | IRShift mk f => imonad_pure (IRShift (MKHandle mk t1 t2 e k) f)
  | IRControl mk f => imonad_pure (IRControl (MKHandle mk t1 t2 e k) f)
  | IRRaise _ _ => imonad_pure r
  | IRPerform mk tag v =>
      match interpret_eff_term_under e self t2 k tag v (VMKHandle mk t1 t2 e) with
      | Some m => m
      | None => imonad_pure (IRPerform (MKHandle mk t1 t2 e k) tag v)
      end
  end.

Definition unwind_shallow_handle (e : env) (self : interpreter) (t1 : ret_term) (t2 : eff_term) (k : ikont) (r : iresult) : imonad iresult :=
  match r with
  | IRVal v => interpret_ret_term_under e self t1 k v
  | IRShift mk f => imonad_pure (IRShift (MKShallowHandle mk t1 t2 e k) f)
  | IRControl mk f => imonad_pure (IRControl (MKShallowHandle mk t1 t2 e k) f)
  | IRRaise _ _ => imonad_pure r
  | IRPerform mk tag v =>
      match interpret_eff_term_under e self t2 k tag v (VMKPure mk) with
      | Some m => m
      | None => imonad_pure (IRPerform (MKShallowHandle mk t1 t2 e k) tag v)
      end
  end.

Fixpoint interpret_kont_app (self : interpreter) (k1 : kont) (k2 : ikont) (v : val) : imonad iresult :=
  match k1 with
  | KNil => ikont_app k2 v
  | KSeq t e k1' => imonad_under_env e (self t (IKont (KApp k1' k2) (interpret_kont_app self k1' k2)))
  | KLet b t e k1' => imonad_under_env (with_binder b v e) (self t (IKont (KApp k1' k2) (interpret_kont_app self k1' k2)))
  | KApp k11 k12 => interpret_kont_app self k11 (IKont (KApp k12 k2) (interpret_kont_app self k12 k2)) v
  end.

Fixpoint interpret_kont (self : interpreter) (k : kont) (v : val) : imonad iresult :=
  match k with
  | KNil => imonad_pure (IRVal v)
  | KSeq t e k' => imonad_under_env e (self t (IKont k' (interpret_kont self k')))
  | KLet b t e k' => imonad_under_env (with_binder b v e) (self t (IKont k' (interpret_kont self k')))
  | KApp k1 k2 => interpret_kont_app self k1 (IKont k2 (interpret_kont self k2)) v
  end.

Definition refine_kont (self : interpreter) (k : kont) : ikont :=
  IKont k (interpret_kont self k).

Definition refine_kont_app (self : interpreter) (k1 : kont) (k2 : ikont) : ikont :=
  IKont (KApp k1 k2) (interpret_kont_app self k1 k2).

Fixpoint interpret_metakont (self : interpreter) (mk : metakont) (v : val) : imonad iresult :=
  match mk with
  | MKPure k => interpret_kont self k v
  | MKReset mk' k => interpret_metakont self mk' v >>= unwind_reset (refine_kont self k)
  | MKPrompt mk' k => interpret_metakont self mk' v >>= unwind_prompt (refine_kont self k)
  | MKTry mk' t e k => interpret_metakont self mk' v >>= unwind_try e self t (refine_kont self k)
  | MKHandle mk' t1 t2 e k => interpret_metakont self mk' v >>= unwind_handle e self t1 t2 (refine_kont self k)
  | MKShallowHandle mk' t1 t2 e k => interpret_metakont self mk' v >>= unwind_shallow_handle e self t1 t2 (refine_kont self k)
  end.

Definition interpret_metakont_app (self : interpreter) (mk : metakont) (k : ikont) (v : val) : imonad iresult :=
  match mk with
  | MKPure k' => interpret_kont_app self k' k v
  | MKReset mk' k' => interpret_metakont self mk' v >>= unwind_reset (refine_kont_app self k' k)
  | MKPrompt mk' k' => interpret_metakont self mk' v >>= unwind_prompt (refine_kont_app self k' k)
  | MKTry mk' t e k' => interpret_metakont self mk' v >>= unwind_try e self t (refine_kont_app self k' k)
  | MKHandle mk' t1 t2 e k' => interpret_metakont self mk' v >>= unwind_handle e self t1 t2 (refine_kont_app self k' k)
  | MKShallowHandle mk' t1 t2 e k' => interpret_metakont self mk' v >>= unwind_shallow_handle e self t1 t2 (refine_kont_app self k' k)
  end.

Fixpoint interpret_variant_term_under (e : env) (self : interpreter) (t : variant_term) (k : ikont) (tag : tag) (v : val) : imonad iresult :=
  match t with
  | TVariantNil => imonad_throw_error (Match_failure "")
  | TVariantCons p t1 t2 =>
      match match_variant p tag v e with
      | Some e' => imonad_under_env e' (self t1 k)
      | None => interpret_variant_term_under e self t2 k tag v
      end
  end.

Fixpoint interpret_fix_mut_term_under (e : env) (self : interpreter) (t : fix_mut_term) (k : ikont) (f : var) (v : val) : imonad iresult :=
  match t with
  | TFixMutLast f' b t' =>
      if var_eqb f f'
      then imonad_under_env (with_binder b v e) (self t' k)
      else imonad_throw_error (Name_error (var_car f))
  | TFixMutCons f' b t1 t2 =>
      if var_eqb f f'
      then imonad_under_env (with_binder b v e) (self t1 k)
      else interpret_fix_mut_term_under e self t2 k f v
  end.

Definition interpret_term (self : interpreter) : term -> ikont -> imonad iresult :=
  fix self' (t : term) (k : ikont) : imonad iresult :=
    match t with
    | TVal tv => interpret_val_term tv >>= ikont_app k
    | TApp t1 t2 =>
        u <- interpret_val_term t1;
        c <- unwrap_vclosure u;
        v <- interpret_val_term t2;
        match c with
        | CFun b t' e => imonad_under_env (with_binder b v e) (self t' k)
        | CFix f b t' e => imonad_under_env (with_binder b v (ECons f u e)) (self t' k)
        | CFixMut t' f e => interpret_fix_mut_term_under (with_fix_mut_term t' e) self t' k f v
        | CMKPure mk => interpret_metakont_app self mk k v
        | CMKReset mk => interpret_metakont self mk v >>= unwind_reset k
        | CMKHandle mk t1' t2' e => interpret_metakont self mk v >>= unwind_handle e self t1' t2' k
        end
    | TSeq t1 t2 =>
        e <- imonad_ask_env;
        self' t1 (IKont (KSeq t2 e k) (fun _ => imonad_under_env e (self' t2 k)))
    | TLet b t1 t2 =>
        e <- imonad_ask_env;
        self' t1 (IKont (KLet b t2 e k) (fun v => imonad_under_env (with_binder b v e) (self' t2 k)))
    | TIf tv t1 t2 =>
        v <- interpret_val_term tv;
        b <- unwrap_vbool v;
        if b then self' t1 k else self' t2 k
    | TSplit b1 b2 tv t' =>
        v <- interpret_val_term tv;
        '(v1, v2) <- unwrap_vprod v;
        imonad_local_env (fun e => with_binder b2 v2 (with_binder b1 v1 e)) (self' t' k)
    | TCase tv b1 t1 b2 t2 =>
        v <- interpret_val_term tv;
        s <- unwrap_vsum v;
        match s with
        | inl v' => imonad_local_env (with_binder b1 v') (self' t1 k)
        | inr v' => imonad_local_env (with_binder b2 v') (self' t2 k)
        end
    | TWhile tv t' =>
        v <- interpret_val_term tv;
        b <- unwrap_vbool v;
        if b then
          e <- imonad_ask_env;
          self' t' (IKont (KSeq t e k) (fun _ => imonad_under_env e (self t k)))
        else ikont_app k VTt
    | TLetFix f b t1 t2 => imonad_local_env (fun e => ECons f (VFix f b t1 e) e) (self' t2 k)
    | TLetFixMut t1 t2 => imonad_local_env (with_fix_mut_term t1) (self' t2 k)
    | TLetTuple p tv t' =>
        v <- interpret_val_term tv;
        t <- unwrap_vtuple v;
        e <- imonad_ask_env;
        match match_tuple p t e with
        | Some e' => imonad_under_env e' (self' t' k)
        | None => imonad_throw_error (Match_failure "")
        end
    | TLetRecord p tv t' =>
        v <- interpret_val_term tv;
        r <- unwrap_vrecord v;
        e <- imonad_ask_env;
        match match_record p r e with
        | Some e' => imonad_under_env e' (self' t' k)
        | None => imonad_throw_error (Match_failure "")
        end
    | TMatchVariant tv t' =>
        v <- interpret_val_term tv;
        '(Variant tag v') <- unwrap_vvariant v;
        e <- imonad_ask_env;
        interpret_variant_term_under e self' t' k tag v'
    | TShift b t' => imonad_asks_env (fun e => IRShift (MKPure k) (fun u => imonad_under_env (with_binder b u e) (self' t' ikont_nil)))
    | TReset t' => self' t' ikont_nil >>= unwind_reset k
    | TControl b t' => imonad_asks_env (fun e => IRControl (MKPure k) (fun u => imonad_under_env (with_binder b u e) (self' t' ikont_nil)))
    | TPrompt t' => self' t' ikont_nil >>= unwind_prompt k
    | TRaise t' =>
        v <- interpret_val_term t';
        IRRaise' <$> unwrap_vexn v
    | TTry t1 t2 =>
        r <- self' t1 ikont_nil;
        e <- imonad_ask_env;
        unwind_try e self' t2 k r
    | TPerform t' =>
        v <- interpret_val_term t';
        IRPerform' (MKPure k) <$> unwrap_veff v
    | THandle t1 t2 t3 =>
        r <- self' t1 ikont_nil;
        e <- imonad_ask_env;
        unwind_handle e self' t2 t3 k r
    | TShallowHandle t1 t2 t3 =>
        r <- self' t1 ikont_nil;
        e <- imonad_ask_env;
        unwind_shallow_handle e self' t2 t3 k r
    end.

Fixpoint interpret_term' (fuel : nat) (t : term) (k : ikont) : imonad iresult :=
  match fuel with
  | O => imonad_throw_error Out_of_fuel
  | S fuel' => interpret_term (interpret_term' fuel') t k
  end.

Definition unwrap_IRVal (r : iresult) : imonad val :=
  match r with
  | IRVal v => imonad_pure v
  | IRShift _ _ => imonad_throw_error (Undelimited_shift "")
  | IRControl _ _ => imonad_throw_error (Undelimited_control "")
  | IRRaise _ _ => imonad_throw_error (Unhandled_exception "")
  | IRPerform _ _ _ => imonad_throw_error (Unhandled_effect "")
  end.

Definition run_term (fuel : nat) (t : term) : (ierror + val) * iheap :=
  imonad_run (interpret_term' fuel t ikont_nil >>= unwrap_IRVal) ENil iheap_empty.

Definition eval_term (fuel : nat) (t : term) : ierror + val :=
  fst (run_term fuel t).

Definition exec_term (fuel : nat) (t : term) : iheap :=
  snd (run_term fuel t).
