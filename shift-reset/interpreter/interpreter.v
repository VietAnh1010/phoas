From Stdlib Require Import String Qcanon ZArith.
From shift_reset.core Require Import syntax env kont loc tag val var.
From shift_reset.interpreter Require Import dispatch ierror iheap imonad unwrap.

Local Open Scope string_scope.
Local Open Scope imonad_scope.
Local Unset Elimination Schemes.

Fixpoint interpret_val_term (t : val_term) : imonad val :=
  match t with
  | TVVar x =>
      env <- imonad_ask_env;
      match env_lookup x env with
      | None => imonad_throw_error (Name_error x)
      | Some v => imonad_pure v
      end
  | TVUnit => imonad_pure VUnit
  | TVInt z => imonad_pure (VInt z)
  | TVFloat q => imonad_pure (VFloat q)
  | TVNeg t' => interpret_val_term t' >>= dispatch_neg
  | TVAdd t1 t2 => v <- interpret_val_term t1; f <- dispatch_add v; interpret_val_term t2 >>= f
  | TVSub t1 t2 => v <- interpret_val_term t1; f <- dispatch_sub v; interpret_val_term t2 >>= f
  | TVMul t1 t2 => v <- interpret_val_term t1; f <- dispatch_mul v; interpret_val_term t2 >>= f
  | TVDiv t1 t2 => v <- interpret_val_term t1; f <- dispatch_div v; interpret_val_term t2 >>= f
  | TVMod t1 t2 => v <- interpret_val_term t1; f <- dispatch_mod v; interpret_val_term t2 >>= f
  | TVTrue => imonad_pure VTrue
  | TVFalse => imonad_pure VFalse
  | TVNot t' => interpret_val_term t' >>= dispatch_not
  | TVAnd t1 t2 =>
      v <- interpret_val_term t1;
      b <- unwrap_vbool v;
      if b then interpret_val_term t2 else imonad_pure VFalse
  | TVOr t1 t2 =>
      v <- interpret_val_term t1;
      b <- unwrap_vbool v;
      if b then imonad_pure VTrue else interpret_val_term t2
  | TVFun t' => imonad_asks_env (VFun' t')
  | TVFix t' => imonad_asks_env (VFix' t')
  | TVPair t1 t2 => v <- interpret_val_term t1; VPair v <$> interpret_val_term t2
  | TVInl t' => VInl <$> interpret_val_term t'
  | TVInr t' => VInr <$> interpret_val_term t'
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
      | Some h' => VUnit <$ imonad_set_heap h'
      end
  | TVFree t' =>
      v <- interpret_val_term t';
      l <- unwrap_vref v;
      h <- imonad_get_heap;
      match iheap_free l h with
      | None => imonad_throw_error (Memory_error "free")
      | Some h' => VUnit <$ imonad_set_heap h'
      end
  | TVExn tag t' => VExn' tag <$> interpret_val_term t'
  | TVEff tag t' => VEff' tag <$> interpret_val_term t'
  | TVAssert t' =>
      v <- interpret_val_term t';
      b <- unwrap_vbool v;
      if b then imonad_pure VUnit else imonad_throw_error (Assert_failure "")
  | TVLt t1 t2 => v <- interpret_val_term t1; f <- dispatch_lt v; interpret_val_term t2 >>= f
  | TVLe t1 t2 => v <- interpret_val_term t1; f <- dispatch_le v; interpret_val_term t2 >>= f
  | TVGt t1 t2 => v <- interpret_val_term t1; f <- dispatch_gt v; interpret_val_term t2 >>= f
  | TVGe t1 t2 => v <- interpret_val_term t1; f <- dispatch_ge v; interpret_val_term t2 >>= f
  | TVEq t1 t2 => v <- interpret_val_term t1; f <- dispatch_eq v; interpret_val_term t2 >>= f
  | TVNeq t1 t2 => v <- interpret_val_term t1; f <- dispatch_neq v; interpret_val_term t2 >>= f
  end.

Inductive iresult : Type :=
| RVal : val -> iresult
| RShift : metakont -> (val -> imonad iresult) -> tag -> iresult
| RControl : metakont -> (val -> imonad iresult) -> tag -> iresult
| RRaise : exn -> iresult
| RPerform : metakont -> eff -> iresult.

Definition with_binder (b : binder) (v : val) (m : imonad iresult) : imonad iresult :=
  match b with
  | BAny => m
  | BVar x => imonad_local_env (EnvCons x v) m
  end.

Definition with_binder2 (b1 b2 : binder) (v1 v2 : val) (m : imonad iresult) : imonad iresult :=
  with_binder b2 v2 (with_binder b1 v1 m).

Fixpoint match_exn (p : pattern) (exn : exn) : option (imonad iresult -> imonad iresult) :=
  match p with
  | PAny => Some (fun m => m)
  | PVar x => Some (imonad_local_env (EnvCons x (VExn exn)))
  | PConstr tag b =>
      let (tag', v) := exn in
      if tag_eqb tag tag' then Some (with_binder b v) else None
  | PAlias p' x =>
      match match_exn p' exn with
      | Some f => Some (fun m => imonad_local_env (EnvCons x (VExn exn)) (f m))
      | None => None
      end
  end.

Fixpoint match_eff (p : pattern) (b : binder) (eff : eff) (v : val) : option (imonad iresult -> imonad iresult) :=
  match p with
  | PAny => Some (with_binder b v)
  | PVar x => Some (fun m => imonad_local_env (EnvCons x (VEff eff)) (with_binder b v m))
  | PConstr tag b' =>
      let (tag', v') := eff in
      if tag_eqb tag tag' then Some (with_binder2 b b' v v') else None
  | PAlias p' x =>
      match match_eff p' b eff v with
      | Some f => Some (fun m => imonad_local_env (EnvCons x (VEff eff)) (f m))
      | None => None
      end
  end.

Record ikont : Type := IKont { ikont_car :> kont; ikont_app :> val -> imonad iresult }.
Definition interpreter : Type := ikont -> term -> imonad iresult.

Fixpoint unwind_reset (tag : tag) (k : ikont) (r : iresult) : imonad iresult :=
  match r with
  | RVal v => k v
  | RShift mk f tag' =>
      if tag_eqb tag tag'
      then f (VMKReset mk tag) >>= unwind_reset tag k
      else imonad_pure (RShift (MKReset mk tag k) f tag')
  | RControl mk f tag' => imonad_pure (RControl (MKReset mk tag k) f tag')
  | RRaise _ => imonad_pure r
  | RPerform mk eff => imonad_pure (RPerform (MKReset mk tag k) eff)
  end.

Fixpoint unwind_prompt (tag : tag) (k : ikont) (r : iresult) : imonad iresult :=
  match r with
  | RVal v => k v
  | RShift mk f tag' => imonad_pure (RShift (MKPrompt mk tag k) f tag')
  | RControl mk f tag' =>
      if tag_eqb tag tag'
      then f (VMKPure mk) >>= unwind_prompt tag k
      else imonad_pure (RControl (MKPrompt mk tag k) f tag')
  | RRaise _ => imonad_pure r
  | RPerform mk eff => imonad_pure (RPerform (MKPrompt mk tag k) eff)
  end.

Definition interpret_abs_term_with (self : interpreter) (k : ikont) (t : abs_term) (v : val) : imonad iresult :=
  let (b, t') := t in with_binder b v (self k t').

Definition interpret_abs2_term_with (self : interpreter) (k : ikont) (t : abs2_term) (v1 v2 : val) : imonad iresult :=
  let (b1, b2, t') := t in with_binder2 b1 b2 v1 v2 (self k t').

Definition interpret_ret_term_with (self : interpreter) (k : ikont) (t : ret_term) (v : val) : imonad iresult :=
  match t with
  | TRetNone => k v
  | TRetSome b t' => with_binder b v (self k t')
  end.

Fixpoint interpret_exn_term_with (self : interpreter) (k : ikont) (t : exn_term) (exn : exn) : option (imonad iresult) :=
  match t with
  | TExnLast p t' =>
      match match_exn p exn with
      | Some f => Some (f (self k t'))
      | None => None
      end
  | TExnCons p t1 t2 =>
      match match_exn p exn with
      | Some f => Some (f (self k t1))
      | None => interpret_exn_term_with self k t2 exn
      end
  end.

Fixpoint interpret_eff_term_with (self : interpreter) (k : ikont) (t : eff_term) (eff : eff) (v : val) : option (imonad iresult) :=
  match t with
  | TEffLast p b t' =>
      match match_eff p b eff v with
      | Some f => Some (f (self k t'))
      | None => None
      end
  | TEffCons p b t1 t2 =>
      match match_eff p b eff v with
      | Some f => Some (f (self k t1))
      | None => interpret_eff_term_with self k t2 eff v
      end
  end.

Definition interpret_kont_clo_with (self : interpreter) (k : ikont) (c : kont_clo) (v : val) : imonad iresult :=
  match c with
  | CKSeq env t => imonad_use_env env (self k t)
  | CKLet env t => imonad_use_env env (interpret_abs_term_with self k t v)
  end.

Fixpoint append_ikont (self : interpreter) (k1 : kont) (k2 : ikont) : ikont :=
  match k1 with
  | KNil => k2
  | KCons c k1' =>
      let k := append_ikont self k1' k2 in
      IKont (KCons c k) (interpret_kont_clo_with self k c)
  end.

Definition unwind_try (self : interpreter) (c : try_clo) (k : ikont) (r : iresult) : imonad iresult :=
  match r with
  | RVal v => k v
  | RShift mk f tag => imonad_pure (RShift (MKTry mk c k) f tag)
  | RControl mk f tag => imonad_pure (RControl (MKTry mk c k) f tag)
  | RRaise exn =>
      let (_, t) := c in
      match interpret_exn_term_with self k t exn with
      | Some m => m
      | None => imonad_pure r
      end
  | RPerform mk eff => imonad_pure (RPerform (MKTry mk c k) eff)
  end.

Definition unwind_try_clo (self : interpreter) (c : try_clo) (k : ikont) (r : iresult) : imonad iresult :=
  let (env, _) := c in imonad_use_env env (unwind_try self c k r).

Definition unwind_handle (self : interpreter) (c : handle_clo) (k : ikont) (r : iresult) : imonad iresult :=
  match r with
  | RVal v => let (_, t, _) := c in interpret_ret_term_with self k t v
  | RShift mk f tag => imonad_pure (RShift (MKHandle mk c k) f tag)
  | RControl mk f tag => imonad_pure (RControl (MKHandle mk c k) f tag)
  | RRaise _ => imonad_pure r
  | RPerform mk eff =>
      let (_, _, t) := c in
      match interpret_eff_term_with self k t eff (VMKHandle mk c) with
      | Some m => m
      | None => imonad_pure (RPerform (MKHandle mk c k) eff)
      end
  end.

Definition unwind_handle_clo (self : interpreter) (c : handle_clo) (k : ikont) (r : iresult) : imonad iresult :=
  let (env, _, _) := c in imonad_use_env env (unwind_handle self c k r).

Definition unwind_shallow_handle (self : interpreter) (c : shallow_handle_clo) (k : ikont) (r : iresult) : imonad iresult :=
  match r with
  | RVal v => let (_, t, _) := c in interpret_ret_term_with self k t v
  | RShift mk f tag => imonad_pure (RShift (MKShallowHandle mk c k) f tag)
  | RControl mk f tag => imonad_pure (RControl (MKShallowHandle mk c k) f tag)
  | RRaise _ => imonad_pure r
  | RPerform mk eff =>
      let (_, _, t) := c in
      match interpret_eff_term_with self k t eff (VMKPure mk) with
      | Some m => m
      | None => imonad_pure (RPerform (MKShallowHandle mk c k) eff)
      end
  end.

Definition unwind_shallow_handle_clo (self : interpreter) (c : shallow_handle_clo) (k : ikont) (r : iresult) : imonad iresult :=
  let (env, _, _) := c in imonad_use_env env (unwind_shallow_handle self c k r).

Fixpoint interpret_kont_with (self : interpreter) (k : kont) (v : val) : imonad iresult :=
  match k with
  | KNil => imonad_pure (RVal v)
  | KCons c k' => interpret_kont_clo_with self (IKont k' (interpret_kont_with self k')) c v
  end.

Definition refine_kont (self : interpreter) (k : kont) : ikont :=
  IKont k (interpret_kont_with self k).

Fixpoint interpret_metakont_with (self : interpreter) (mk : metakont) (v : val) : imonad iresult :=
  match mk with
  | MKPure k => interpret_kont_with self k v
  | MKReset mk' tag k => interpret_metakont_with self mk' v >>= unwind_reset tag (refine_kont self k)
  | MKPrompt mk' tag k => interpret_metakont_with self mk' v >>= unwind_prompt tag (refine_kont self k)
  | MKTry mk' c k => interpret_metakont_with self mk' v >>= unwind_try_clo self c (refine_kont self k)
  | MKHandle mk' c k => interpret_metakont_with self mk' v >>= unwind_handle_clo self c (refine_kont self k)
  | MKShallowHandle mk' c k => interpret_metakont_with self mk' v >>= unwind_shallow_handle_clo self c (refine_kont self k)
  end.

Definition ikont_nil : ikont := IKont KNil (fun v => imonad_pure (RVal v)).

Definition refine_term (self : interpreter) (k : ikont) (t : term) (env : env) (_ : val) : imonad iresult :=
  imonad_use_env env (self k t).

Definition refine_abs_term (self : interpreter) (k : ikont) (t : abs_term) (env : env) (v : val) : imonad iresult :=
  imonad_use_env env (interpret_abs_term_with self k t v).

Definition app_LFun (self : interpreter) (k : ikont) (c : fun_clo) (v : val) : imonad iresult :=
  let (env, t) := c in imonad_use_env env (interpret_abs_term_with self k t v).

Definition app_LFix (self : interpreter) (k : ikont) (c : fix_clo) (u v : val) : imonad iresult :=
  let (env, t) := c in imonad_use_env env (interpret_abs2_term_with self k t u v).

Definition app_LMKPure (self : interpreter) (k : ikont) (mk : metakont) (v : val) : imonad iresult :=
  match mk with
  | MKPure k' => append_ikont self k' k v
  | MKReset mk' tag k' => interpret_metakont_with self mk' v >>= unwind_reset tag (append_ikont self k' k)
  | MKPrompt mk' tag k' => interpret_metakont_with self mk' v >>= unwind_prompt tag (append_ikont self k' k)
  | MKTry mk' c k' => interpret_metakont_with self mk' v >>= unwind_try_clo self c (append_ikont self k' k)
  | MKHandle mk' c k' => interpret_metakont_with self mk' v >>= unwind_handle_clo self c (append_ikont self k' k)
  | MKShallowHandle mk' c k' => interpret_metakont_with self mk' v >>= unwind_shallow_handle_clo self c (append_ikont self k' k)
  end.

Definition app_LMKReset (self : interpreter) (k : ikont) (mk : metakont) (tag : tag) (v : val) : imonad iresult :=
  interpret_metakont_with self mk v >>= unwind_reset tag k.

Definition app_LMKHandle (self : interpreter) (k : ikont) (mk : metakont) (c : handle_clo) (v : val) : imonad iresult :=
  interpret_metakont_with self mk v >>= unwind_handle_clo self c k.

Definition interpret_term_aux (self' : interpreter) : ikont -> term -> imonad iresult :=
  fix self k t :=
    match t with
    | TVal t' => interpret_val_term t' >>= k
    | TApp t1 t2 =>
        u <- interpret_val_term t1;
        l <- unwrap_vlambda u;
        v <- interpret_val_term t2;
        match l with
        | LFun c => app_LFun self' k c v
        | LFix c => app_LFix self' k c u v
        | LMKPure mk => app_LMKPure self' k mk v
        | LMKReset mk tag => app_LMKReset self' k mk tag v
        | LMKHandle mk c => app_LMKHandle self' k mk c v
        end
    | TSeq t1 t2 => env <- imonad_ask_env; self (IKont (KCons (CKSeq env t2) k) (refine_term self k t2 env)) t1
    | TLet t1 t2 => env <- imonad_ask_env; self (IKont (KCons (CKLet env t2) k) (refine_abs_term self k t2 env)) t1
    | TIf t1 t2 t3 =>
        v <- interpret_val_term t1;
        b <- unwrap_vbool v;
        if b then self k t2 else self k t3
    | TSplit t1 t2 =>
        v <- interpret_val_term t1;
        p <- unwrap_vprod v;
        let (v1, v2) := p in interpret_abs2_term_with self k t2 v1 v2
    | TCase t1 t2 t3 =>
        v <- interpret_val_term t1;
        s <- unwrap_vsum v;
        match s with
        | inl v' => interpret_abs_term_with self k t2 v'
        | inr v' => interpret_abs_term_with self k t3 v'
        end
    | TShift tag t' => imonad_asks_env (fun env => RShift (MKPure k) (refine_abs_term self ikont_nil t' env) tag)
    | TReset tag t' => self ikont_nil t' >>= unwind_reset tag k
    | TControl tag t' => imonad_asks_env (fun env => RControl (MKPure k) (refine_abs_term self ikont_nil t' env) tag)
    | TPrompt tag t' => self ikont_nil t' >>= unwind_prompt tag k
    | TRaise t' =>
        v <- interpret_val_term t';
        RRaise <$> unwrap_vexn v
    | TTry t1 t2 =>
        r <- self ikont_nil t1;
        env <- imonad_ask_env;
        unwind_try self (CTry env t2) k r
    | TPerform t' =>
        v <- interpret_val_term t';
        RPerform (MKPure k) <$> unwrap_veff v
    | THandle t1 t2 t3 =>
        r <- self ikont_nil t1;
        env <- imonad_ask_env;
        unwind_handle self (CHandle env t2 t3) k r
    | TShallowHandle t1 t2 t3 =>
        r <- self ikont_nil t1;
        env <- imonad_ask_env;
        unwind_shallow_handle self (CShallowHandle env t2 t3) k r
    end.

Fixpoint interpret_term (fuel : nat) (k : ikont) (t : term) : imonad iresult :=
  match fuel with
  | O => imonad_throw_error Out_of_fuel
  | S fuel' => interpret_term_aux (interpret_term fuel') k t
  end.

Definition unwrap_RVal (r : iresult) : imonad val :=
  match r with
  | RVal v => imonad_pure v
  | RShift _ _ tag => imonad_throw_error (Undelimited_shift tag)
  | RControl _ _ tag => imonad_throw_error (Undelimited_control tag)
  | RRaise exn => imonad_throw_error (Unhandled_exception exn)
  | RPerform _ eff => imonad_throw_error (Unhandled_effect eff)
  end.

Definition run_term (fuel : nat) (t : term) : (ierror + val) * iheap :=
  imonad_run (interpret_term fuel ikont_nil t >>= unwrap_RVal) EnvNil iheap_empty.

Definition eval_term (fuel : nat) (t : term) : ierror + val :=
  fst (run_term fuel t).

Definition exec_term (fuel : nat) (t : term) : iheap :=
  snd (run_term fuel t).
