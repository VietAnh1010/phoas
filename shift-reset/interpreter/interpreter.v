From Stdlib Require Import String Qcanon ZArith.
From shift_reset.core Require Import syntax env loc tag val var.
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
  | TVTrue => imonad_pure VTrue
  | TVFalse => imonad_pure VFalse
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
  | TVPair t1 t2 =>
      v <- interpret_val_term t1;
      VPair v <$> interpret_val_term t2
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
  | TVOp1 op t' => interpret_val_term t' >>= dispatch_op1 op
  | TVOp2 op t1 t2 =>
      v <- interpret_val_term t1;
      f <- dispatch_op2 op v;
      interpret_val_term t2 >>= f
  end.

Definition with_binder (b : binder) (v : val) (env : env) : syntax.env :=
  match b with
  | BAny => env
  | BVar x => EnvCons x v env
  end.

Fixpoint match_exn (p : pattern) (exn : exn) (env : env) : option syntax.env :=
  match p with
  | PAny => Some env
  | PVar x => Some (EnvCons x (VExn exn) env)
  | PConstr tag b =>
      let (tag', v) := exn in
      if tag_eqb tag tag' then Some (with_binder b v env) else None
  | PAlias p' x =>
      match match_exn p' exn env with
      | Some env' => Some (EnvCons x (VExn exn) env')
      | None => None
      end
  end.

Fixpoint match_eff (p : pattern) (b : binder) (eff : eff) (v : val) (env : env) : option syntax.env :=
  match p with
  | PAny => Some (with_binder b v env)
  | PVar x => Some (EnvCons x (VEff eff) (with_binder b v env))
  | PConstr tag b' =>
      let (tag', v') := eff in
      if tag_eqb tag tag' then Some (with_binder b' v' (with_binder b v env)) else None
  | PAlias p' x =>
      match match_eff p' b eff v env with
      | Some env' => Some (EnvCons x (VEff eff) env')
      | None => None
      end
  end.

Inductive iresult : Type :=
| IRVal : val -> iresult
| IRShift : metakont -> (val -> imonad iresult) -> tag -> iresult
| IRControl : metakont -> (val -> imonad iresult) -> tag -> iresult
| IRRaise : exn -> iresult
| IRPerform : metakont -> eff -> iresult.

Record ikont : Type := IKont { ikont_car :> kont; ikont_app :> val -> imonad iresult }.

Definition ikont_nil : ikont := IKont KNil (fun v => imonad_pure (IRVal v)).

Definition interpreter : Type := term -> ikont -> imonad iresult.

Fixpoint unwind_reset (tag : tag) (k : ikont) (r : iresult) : imonad iresult :=
  match r with
  | IRVal v => k v
  | IRShift mk f tag' =>
      if tag_eqb tag tag'
      then f (VMKReset mk tag) >>= unwind_reset tag k
      else imonad_pure (IRShift (MKReset mk tag k) f tag')
  | IRControl mk f tag' => imonad_pure (IRControl (MKReset mk tag k) f tag')
  | IRRaise _ => imonad_pure r
  | IRPerform mk eff => imonad_pure (IRPerform (MKReset mk tag k) eff)
  end.

Fixpoint unwind_prompt (tag : tag) (k : ikont) (r : iresult) : imonad iresult :=
  match r with
  | IRVal v => k v
  | IRShift mk f tag' => imonad_pure (IRShift (MKPrompt mk tag k) f tag')
  | IRControl mk f tag' =>
      if tag_eqb tag tag'
      then f (VMKPure mk) >>= unwind_prompt tag k
      else imonad_pure (IRControl (MKPrompt mk tag k) f tag')
  | IRRaise _ => imonad_pure r
  | IRPerform mk eff => imonad_pure (IRPerform (MKPrompt mk tag k) eff)
  end.

Definition interpret_term1_aux (self : interpreter) (t : term1) (k : ikont) (v : val) : imonad iresult :=
  let (b, t') := t in imonad_local_env (with_binder b v) (self t' k).

Definition interpret_term2_aux (self : interpreter) (t : term2) (k : ikont) (v1 v2 : val) : imonad iresult :=
  let (b1, b2, t') := t in imonad_local_env (fun env => with_binder b2 v2 (with_binder b1 v1 env)) (self t' k).

Definition interpret_term1_aux_under (env : env) (self : interpreter) (t : term1) (k : ikont) (v : val) : imonad iresult :=
  let (b, t') := t in imonad_under_env (with_binder b v env) (self t' k).

Definition interpret_term2_aux_under (env : env) (self : interpreter) (t : term2) (k : ikont) (v1 v2 : val) : imonad iresult :=
  let (b1, b2, t') := t in imonad_under_env (with_binder b2 v2 (with_binder b1 v1 env)) (self t' k).

Definition interpret_ret_term_aux_under (env : env) (self : interpreter) (t : ret_term) (k : ikont) (v : val) : imonad iresult :=
  match t with
  | TRetNone => k v
  | TRetSome b t' => imonad_under_env (with_binder b v env) (self t' k)
  end.

Fixpoint interpret_exn_term_aux_under (env : env) (self : interpreter) (t : exn_term) (k : ikont) (exn : exn) : option (imonad iresult) :=
  match t with
  | TExnLast p t' =>
      match match_exn p exn env with
      | Some env' => Some (imonad_under_env env' (self t' k))
      | None => None
      end
  | TExnCons p t1 t2 =>
      match match_exn p exn env with
      | Some env' => Some (imonad_under_env env' (self t1 k))
      | None => interpret_exn_term_aux_under env self t2 k exn
      end
  end.

Fixpoint interpret_eff_term_aux_under (env : env) (self : interpreter) (t : eff_term) (k : ikont) (eff : eff) (v : val) : option (imonad iresult) :=
  match t with
  | TEffLast p b t' =>
      match match_eff p b eff v env with
      | Some env' => Some (imonad_under_env env' (self t' k))
      | None => None
      end
  | TEffCons p b t1 t2 =>
      match match_eff p b eff v env with
      | Some env' => Some (imonad_under_env env' (self t1 k))
      | None => interpret_eff_term_aux_under env self t2 k eff v
      end
  end.

Definition unwind_try (self : interpreter) (c : try_clo) (k : ikont) (r : iresult) : imonad iresult :=
  match r with
  | IRVal v => k v
  | IRShift mk f tag => imonad_pure (IRShift (MKTry mk c k) f tag)
  | IRControl mk f tag => imonad_pure (IRControl (MKTry mk c k) f tag)
  | IRRaise exn =>
      let (env, t) := c in
      match interpret_exn_term_aux_under env self t k exn with
      | Some m => m
      | None => imonad_pure r
      end
  | IRPerform mk eff => imonad_pure (IRPerform (MKTry mk c k) eff)
  end.

Definition unwind_handle (self : interpreter) (c : handle_clo) (k : ikont) (r : iresult) : imonad iresult :=
  match r with
  | IRVal v => let (env, t, _) := c in interpret_ret_term_aux_under env self t k v
  | IRShift mk f tag => imonad_pure (IRShift (MKHandle mk c k) f tag)
  | IRControl mk f tag => imonad_pure (IRControl (MKHandle mk c k) f tag)
  | IRRaise _ => imonad_pure r
  | IRPerform mk eff =>
      let (env, _, t) := c in
      match interpret_eff_term_aux_under env self t k eff (VMKHandle mk c) with
      | Some m => m
      | None => imonad_pure (IRPerform (MKHandle mk c k) eff)
      end
  end.

Definition unwind_shallow_handle (self : interpreter) (c : shallow_handle_clo) (k : ikont) (r : iresult) : imonad iresult :=
  match r with
  | IRVal v => let (env, t, _) := c in interpret_ret_term_aux_under env self t k v
  | IRShift mk f tag => imonad_pure (IRShift (MKShallowHandle mk c k) f tag)
  | IRControl mk f tag => imonad_pure (IRControl (MKShallowHandle mk c k) f tag)
  | IRRaise _ => imonad_pure r
  | IRPerform mk eff =>
      let (env, _, t) := c in
      match interpret_eff_term_aux_under env self t k eff (VMKPure mk) with
      | Some m => m
      | None => imonad_pure (IRPerform (MKShallowHandle mk c k) eff)
      end
  end.

Definition interpret_kont_clo_aux (self : interpreter) (c : kont_clo) (k : ikont) (v : val) : imonad iresult :=
  match c with
  | CKSeq env t => imonad_under_env env (self t k)
  | CKLet env t => interpret_term1_aux_under env self t k v
  end.

Fixpoint interpret_kont_aux (self : interpreter) (k : kont) (v : val) : imonad iresult :=
  match k with
  | KNil => imonad_pure (IRVal v)
  | KCons c k' => interpret_kont_clo_aux self c (IKont k' (interpret_kont_aux self k')) v
  | KApp k1 k2 => interpret_kont_aux self (IKont k1 (interpret_kont_aux self k2)) v
  end.

Fixpoint interpret_kont_aux_app (self : interpreter) (k1 : kont) (k2 : ikont) (v : val) : imonad iresult :=
  match k1 with
  | KNil => k2 v
  | KCons c k1' => interpret_kont_clo_aux self c (IKont (KApp k1' k2) (interpret_kont_aux_app self k1' k2)) v
  | KApp k11 k12 => interpret_kont_aux_app self k11 (IKont (KApp k12 k2) (interpret_kont_aux_app self k12 k2)) v
  end.

Definition refine_kont (self : interpreter) (k : kont) : ikont :=
  IKont k (interpret_kont_aux self k).

Definition refine_kont_app (self : interpreter) (k1 : kont) (k2 : ikont) : ikont :=
  IKont (KApp k1 k2) (interpret_kont_aux_app self k1 k2).

Fixpoint interpret_metakont_aux (self : interpreter) (mk : metakont) (v : val) : imonad iresult :=
  match mk with
  | MKPure k => interpret_kont_aux self k v
  | MKReset mk' tag k => interpret_metakont_aux self mk' v >>= unwind_reset tag (refine_kont self k)
  | MKPrompt mk' tag k => interpret_metakont_aux self mk' v >>= unwind_prompt tag (refine_kont self k)
  | MKTry mk' c k => interpret_metakont_aux self mk' v >>= unwind_try self c (refine_kont self k)
  | MKHandle mk' c k => interpret_metakont_aux self mk' v >>= unwind_handle self c (refine_kont self k)
  | MKShallowHandle mk' c k => interpret_metakont_aux self mk' v >>= unwind_shallow_handle self c (refine_kont self k)
  end.

Definition interpret_metakont_aux_app (self : interpreter) (mk : metakont) (k : ikont) (v : val) : imonad iresult :=
  match mk with
  | MKPure k' => interpret_kont_aux_app self k' k v
  | MKReset mk' tag k' => interpret_metakont_aux self mk' v >>= unwind_reset tag (refine_kont_app self k' k)
  | MKPrompt mk' tag k' => interpret_metakont_aux self mk' v >>= unwind_prompt tag (refine_kont_app self k' k)
  | MKTry mk' c k' => interpret_metakont_aux self mk' v >>= unwind_try self c (refine_kont_app self k' k)
  | MKHandle mk' c k' => interpret_metakont_aux self mk' v >>= unwind_handle self c (refine_kont_app self k' k)
  | MKShallowHandle mk' c k' => interpret_metakont_aux self mk' v >>= unwind_shallow_handle self c (refine_kont_app self k' k)
  end.

Definition interpret_term_aux (self : interpreter) : term -> ikont -> imonad iresult :=
  fix self' (t : term) (k : ikont) : imonad iresult :=
    match t with
    | TVal t' => interpret_val_term t' >>= k
    | TApp t1 t2 =>
        u <- interpret_val_term t1;
        l <- unwrap_vlambda u;
        v <- interpret_val_term t2;
        match l with
        | LFun c => let (env, t) := c in interpret_term1_aux_under env self t k v
        | LFix c => let (env, t) := c in interpret_term2_aux_under env self t k u v
        | LMKPure mk => interpret_metakont_aux_app self mk k v
        | LMKReset mk tag => interpret_metakont_aux self mk v >>= unwind_reset tag k
        | LMKHandle mk c => interpret_metakont_aux self mk v >>= unwind_handle self c k
        end
    | TSeq t1 t2 =>
        env <- imonad_ask_env;
        self' t1 (IKont (KCons (CKSeq env t2) k) (fun _ => imonad_under_env env (self' t2 k)))
    | TLet t1 t2 =>
        env <- imonad_ask_env;
        self' t1 (IKont (KCons (CKLet env t2) k) (interpret_term1_aux_under env self' t2 k))
    | TIf t1 t2 t3 =>
        v <- interpret_val_term t1;
        b <- unwrap_vbool v;
        if b then self' t2 k else self' t3 k
    | TSplit t1 t2 =>
        v <- interpret_val_term t1;
        p <- unwrap_vprod v;
        let (v1, v2) := p in interpret_term2_aux self' t2 k v1 v2
    | TCase t1 t2 t3 =>
        v <- interpret_val_term t1;
        s <- unwrap_vsum v;
        match s with
        | inl v' => interpret_term1_aux self' t2 k v'
        | inr v' => interpret_term1_aux self' t3 k v'
        end
    | TWhile t1 t2 =>
        v <- interpret_val_term t1;
        b <- unwrap_vbool v;
        if b then
          env <- imonad_ask_env;
          self' t2 (IKont (KCons (CKSeq env t) k) (fun _ => imonad_under_env env (self t k)))
        else k VUnit
    | TShift tag t' => imonad_asks_env (fun env => IRShift (MKPure k) (interpret_term1_aux_under env self' t' ikont_nil) tag)
    | TReset tag t' => self' t' ikont_nil >>= unwind_reset tag k
    | TControl tag t' => imonad_asks_env (fun env => IRControl (MKPure k) (interpret_term1_aux_under env self' t' ikont_nil) tag)
    | TPrompt tag t' => self' t' ikont_nil >>= unwind_prompt tag k
    | TRaise t' =>
        v <- interpret_val_term t';
        IRRaise <$> unwrap_vexn v
    | TTry t1 t2 =>
        r <- self' t1 ikont_nil;
        env <- imonad_ask_env;
        unwind_try self' (CTry env t2) k r
    | TPerform t' =>
        v <- interpret_val_term t';
        IRPerform (MKPure k) <$> unwrap_veff v
    | THandle t1 t2 t3 =>
        r <- self' t1 ikont_nil;
        env <- imonad_ask_env;
        unwind_handle self' (CHandle env t2 t3) k r
    | TShallowHandle t1 t2 t3 =>
        r <- self' t1 ikont_nil;
        env <- imonad_ask_env;
        unwind_shallow_handle self' (CShallowHandle env t2 t3) k r
    end.

Fixpoint interpret_term (fuel : nat) (t : term) (k : ikont) : imonad iresult :=
  match fuel with
  | O => imonad_throw_error Out_of_fuel
  | S fuel' => interpret_term_aux (interpret_term fuel') t k
  end.

Definition unwrap_IRVal (r : iresult) : imonad val :=
  match r with
  | IRVal v => imonad_pure v
  | IRShift _ _ tag => imonad_throw_error (Undelimited_shift tag)
  | IRControl _ _ tag => imonad_throw_error (Undelimited_control tag)
  | IRRaise exn => imonad_throw_error (Unhandled_exception exn)
  | IRPerform _ eff => imonad_throw_error (Unhandled_effect eff)
  end.

Definition run_term (fuel : nat) (t : term) : (ierror + val) * iheap :=
  imonad_run (interpret_term fuel t ikont_nil >>= unwrap_IRVal) EnvNil iheap_empty.

Definition eval_term (fuel : nat) (t : term) : ierror + val :=
  fst (run_term fuel t).

Definition exec_term (fuel : nat) (t : term) : iheap :=
  snd (run_term fuel t).
