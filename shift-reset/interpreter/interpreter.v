From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax env kont loc tag val var.
From shift_reset.interpreter Require Import ierror iheap imonad.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope imonad_scope.
Local Unset Elimination Schemes.

Inductive iresult : Type :=
| RReturn : val -> iresult
| RShift : tag -> (val -> imonad iresult) -> metakont -> iresult
| RControl : tag -> (val -> imonad iresult) -> metakont -> iresult
| RRaise : exn -> iresult
| RPerform : eff -> metakont -> iresult.

Definition unwrap_RReturn (r : iresult) : imonad val :=
  match r with
  | RReturn v => imonad_pure v
  | RShift tag _ _ => imonad_throw (ControlError ("undelimited shift: " ++ tag_car tag))
  | RControl tag _ _ => imonad_throw (ControlError ("undelimited control: " ++ tag_car tag))
  | RRaise (Exn tag _) => imonad_throw (ControlError ("unhandled exception: " ++ tag_car tag))
  | RPerform (Eff tag _) _ => imonad_throw (ControlError ("unhandled effect: " ++ tag_car tag))
  end.

Definition unwrap_VInt (v : val) : imonad Z :=
  match v with
  | VInt i => imonad_pure i
  | _ => imonad_throw (TypeError "")
  end.

Definition unwrap_VBool (v : val) : imonad bool :=
  match v with
  | VBool b => imonad_pure b
  | _ => imonad_throw (TypeError "")
  end.

Definition unwrap_VLoc (v : val) : imonad loc :=
  match v with
  | VLoc l => imonad_pure l
  | _ => imonad_throw (TypeError "")
  end.

Definition interpret_atom (a : atom) : imonad val :=
  match a with
  | AUnit => imonad_pure VUnit
  | AInt i => imonad_pure (VInt i)
  | ABool b => imonad_pure (VBool b)
  | AVar x =>
      env <- imonad_ask_env;
      match env_lookup x env with
      | None => imonad_throw (NameError (var_car x))
      | Some v => imonad_pure v
      end
  end.

Definition interpret_i2i (f : Z -> Z) (m : imonad val) : imonad val :=
  imonad_map (fun i => VInt (f i)) (m >>= unwrap_VInt).

Definition interpret_b2b (f : bool -> bool) (m : imonad val) : imonad val :=
  imonad_map (fun b => VBool (f b)) (m >>= unwrap_VBool).

Definition interpret_prim1 (p : prim1) : imonad val -> imonad val :=
  match p with
  | P1Neg => interpret_i2i Z.opp
  | P1Not => interpret_b2b negb
  end.

Definition interpret_ii2i (f : Z -> Z -> Z) (m1 m2 : imonad val) : imonad val :=
  imonad_lift2 (fun i1 i2 => VInt (f i1 i2)) (m1 >>= unwrap_VInt) (m2 >>= unwrap_VInt).

Definition interpret_ii2b (f : Z -> Z -> bool) (m1 m2 : imonad val) : imonad val :=
  imonad_lift2 (fun i1 i2 => VBool (f i1 i2)) (m1 >>= unwrap_VInt) (m2 >>= unwrap_VInt).

Definition interpret_bb2b (f : bool -> bool -> bool) (m1 m2 : imonad val) : imonad val :=
  imonad_lift2 (fun b1 b2 => VBool (f b1 b2)) (m1 >>= unwrap_VBool) (m2 >>= unwrap_VBool).

Definition interpret_vv2b (f : val -> val -> bool) : imonad val -> imonad val -> imonad val :=
  imonad_lift2 (fun v1 v2 => VBool (f v1 v2)).

Definition interpret_prim2 (p : prim2) : imonad val -> imonad val -> imonad val :=
  match p with
  | P2Add => interpret_ii2i Z.add
  | P2Sub => interpret_ii2i Z.sub
  | P2Mul => interpret_ii2i Z.mul
  | P2Div => interpret_ii2i Z.div
  | P2Rem => interpret_ii2i Z.rem
  | P2Lt => interpret_ii2b Z.ltb
  | P2Le => interpret_ii2b Z.leb
  | P2Gt => interpret_ii2b Z.gtb
  | P2Ge => interpret_ii2b Z.geb
  | P2And => interpret_bb2b andb
  | P2Or => interpret_bb2b orb
  | P2Xor => interpret_bb2b xorb
  | P2Eq => interpret_vv2b val_eqb
  | P2Neq => interpret_vv2b val_neqb
  end.

Definition interpret_fun (t : term1) : imonad val :=
  imonad_reader_env (VFun' t).

Definition interpret_fix (t : term2) : imonad val :=
  imonad_reader_env (VFix' t).

Definition interpret_pair : imonad val -> imonad val -> imonad val :=
  imonad_lift2 VPair.

Definition interpret_inl : imonad val -> imonad val :=
  imonad_map VInl.

Definition interpret_inr : imonad val -> imonad val :=
  imonad_map VInr.

Definition interpret_ref (m : imonad val) : imonad val :=
  v <- m;
  h <- imonad_get_heap;
  match iheap_ref v h with
  | None => imonad_throw (MemoryError "")
  | Some (l, h') => VLoc l <$ imonad_set_heap h'
  end.

Definition interpret_get (m : imonad val) : imonad val :=
  l <- m >>= unwrap_VLoc;
  h <- imonad_get_heap;
  match iheap_get l h with
  | None => imonad_throw (MemoryError "")
  | Some v => imonad_pure v
  end.

Definition interpret_set (m1 m2 : imonad val) : imonad val :=
  l <- m1 >>= unwrap_VLoc;
  v <- m2;
  h <- imonad_get_heap;
  match iheap_set l v h with
  | None => imonad_throw (MemoryError "")
  | Some h' => VUnit <$ imonad_set_heap h'
  end.

Definition interpret_free (m : imonad val) : imonad val :=
  l <- m >>= unwrap_VLoc;
  h <- imonad_get_heap;
  match iheap_free l h with
  | None => imonad_throw (MemoryError "")
  | Some h' => VUnit <$ imonad_set_heap h'
  end.

Definition interpret_exn (tag : tag) : imonad val -> imonad val :=
  imonad_map (VExn' tag).

Definition interpret_eff (tag : tag) : imonad val -> imonad val :=
  imonad_map (VEff' tag).

Definition interpret_assert (m : imonad val) : imonad val :=
  b <- m >>= unwrap_VBool;
  if b then imonad_pure VUnit else imonad_throw (ControlError "assertion failure").

Fixpoint interpret_val_term (t : val_term) : imonad val :=
  match t with
  | TVAtom a => interpret_atom a
  | TVFun t' => interpret_fun t'
  | TVFix t' => interpret_fix t'
  | TVPrim1 p t' => interpret_prim1 p (interpret_val_term t')
  | TVPrim2 p t1 t2 => interpret_prim2 p (interpret_val_term t1) (interpret_val_term t2)
  | TVPair t1 t2 => interpret_pair (interpret_val_term t1) (interpret_val_term t2)
  | TVInl t' => interpret_inl (interpret_val_term t')
  | TVInr t' => interpret_inr (interpret_val_term t')
  | TVRef t' => interpret_ref (interpret_val_term t')
  | TVGet t' => interpret_get (interpret_val_term t')
  | TVSet t1 t2 => interpret_set (interpret_val_term t1) (interpret_val_term t2)
  | TVFree t' => interpret_free (interpret_val_term t')
  | TVExn tag t' => interpret_exn tag (interpret_val_term t')
  | TVEff tag t' => interpret_eff tag (interpret_val_term t')
  | TVAssert t' => interpret_assert (interpret_val_term t')
  end.

Definition interpret_let : (env -> imonad iresult) -> imonad iresult :=
  imonad_bind imonad_ask_env.

Definition interpret_seq : (env -> imonad iresult) -> imonad iresult :=
  imonad_bind imonad_ask_env.

Definition interpret_if (m1 : imonad val) (m2 m3 : imonad iresult) : imonad iresult :=
  b <- m1 >>= unwrap_VBool;
  if b then m2 else m3.

Definition interpret_split (m : imonad val) (f : val -> val -> imonad iresult) : imonad iresult :=
  v <- m;
  match v with
  | VPair v1 v2 => f v1 v2
  | _ => imonad_throw (TypeError "")
  end.

Definition interpret_case (m : imonad val) (f1 f2 : val -> imonad iresult) : imonad iresult :=
  v <- m;
  match v with
  | VInl v' => f1 v'
  | VInr v' => f2 v'
  | _ => imonad_throw (TypeError "")
  end.

Fixpoint delimit_reset (tag : tag) (r : iresult) : imonad iresult :=
  match r with
  | RShift tag' f mk => if tag_eq_dec tag tag' then f (VKontReset mk tag) >>= delimit_reset tag else imonad_pure r
  | _ => imonad_pure r
  end.

Fixpoint delimit_prompt (tag : tag) (r : iresult) : imonad iresult :=
  match r with
  | RControl tag' f mk => if tag_eq_dec tag tag' then f (VKont mk) >>= delimit_prompt tag else imonad_pure r
  | _ => imonad_pure r
  end.

Definition interpret_reset (k : kont) (tag : tag) (m : imonad iresult) (f : val -> imonad iresult) : imonad iresult :=
  r <- m >>= delimit_reset tag;
  match r with
  | RReturn v => f v
  | RShift tag' f' mk => imonad_pure (RShift tag' f' (MKReset mk tag k))
  | RControl tag' f' mk => imonad_pure (RControl tag' f' (MKReset mk tag k))
  | RRaise _ => imonad_pure r
  | RPerform eff mk => imonad_pure (RPerform eff (MKReset mk tag k))
  end.

Definition interpret_prompt (k : kont) (tag : tag) (m : imonad iresult) (f : val -> imonad iresult) : imonad iresult :=
  r <- m >>= delimit_prompt tag;
  match r with
  | RReturn v => f v
  | RShift tag' f' mk => imonad_pure (RShift tag' f' (MKPrompt mk tag k))
  | RControl tag' f' mk => imonad_pure (RControl tag' f' (MKPrompt mk tag k))
  | RRaise _ => imonad_pure r
  | RPerform eff mk => imonad_pure (RPerform eff (MKPrompt mk tag k))
  end.

Definition interpret_try (k : kont) (t : exn_term) (m : imonad iresult) (f : val -> imonad iresult)
  (h : exn -> option (imonad iresult)) : imonad iresult :=
  r <- m;
  match r with
  | RReturn v => f v
  | RShift tag f' mk => imonad_reader_env (fun env => RShift tag f' (MKTry' mk t k env))
  | RControl tag f' mk => imonad_reader_env (fun env => RControl tag f' (MKTry' mk t k env))
  | RRaise exn =>
      match h exn with
      | Some m => m
      | None => imonad_pure r
      end
  | RPerform eff mk => imonad_reader_env (fun env => RPerform eff (MKTry' mk t k env))
  end.

Definition interpret_handle (k : kont) (t1 : ret_term) (t2 : eff_term) (m : imonad iresult) (f : val -> imonad iresult)
  (h : eff -> val -> option (imonad iresult)) : imonad iresult :=
  r <- m;
  match r with
  | RReturn v => f v
  | RShift tag f' mk => imonad_reader_env (fun env => RShift tag f' (MKHandle' mk t1 t2 k env))
  | RControl tag f' mk => imonad_reader_env (fun env => RControl tag f' (MKHandle' mk t1 t2 k env))
  | RRaise _ => imonad_pure r
  | RPerform eff mk =>
      env <- imonad_ask_env;
      let c := CHandle env t1 t2 in
      match h eff (VKontHandle mk c) with
      | Some m => m
      | None => imonad_pure (RPerform eff (MKHandle mk c k))
      end
  end.

Definition interpret_shallow_handle (k : kont) (t1 : ret_term) (t2 : eff_term) (m : imonad iresult) (f : val -> imonad iresult)
  (h : eff -> val -> option (imonad iresult)) : imonad iresult :=
  r <- m;
  match r with
  | RReturn v => f v
  | RShift tag f' mk => imonad_reader_env (fun env => RShift tag f' (MKShallowHandle' mk t1 t2 k env))
  | RControl tag f' mk => imonad_reader_env (fun env => RControl tag f' (MKShallowHandle' mk t1 t2 k env))
  | RRaise _ => imonad_pure r
  | RPerform eff mk =>
      match h eff (VKont mk) with
      | Some m => m
      | None => imonad_reader_env (fun env => RPerform eff (MKShallowHandle' mk t1 t2 k env))
      end
  end.

Definition interpret_shift (k : kont) (tag : tag) (f : env -> val -> imonad iresult) : imonad iresult :=
  imonad_reader_env (fun env => RShift tag (f env) (MKPure k)).

Definition interpret_control (k : kont) (tag : tag) (f : env -> val -> imonad iresult) : imonad iresult :=
  imonad_reader_env (fun env => RControl tag (f env) (MKPure k)).

Definition interpret_raise (m : imonad val) : imonad iresult :=
  v <- m;
  match v with
  | VExn exn => imonad_pure (RRaise exn)
  | _ => imonad_throw (TypeError "")
  end.

Definition interpret_perform (k : kont) (m : imonad val) : imonad iresult :=
  v <- m;
  match v with
  | VEff eff => imonad_pure (RPerform eff (MKPure k))
  | _ => imonad_throw (TypeError "")
  end.

Definition with_binder (b : binder) (v : val) (m : imonad iresult) : imonad iresult :=
  match b with
  | BAny => m
  | BVar x => imonad_local_env (EnvCons x v) m
  end.

Fixpoint match_exn (p : pattern) (exn : exn) (m : imonad iresult) : option (imonad iresult) :=
  match p with
  | PAny => Some m
  | PVar x => Some (imonad_local_env (EnvCons x (VExn exn)) m)
  | PConstr tag b =>
      let (tag', v) := exn in
      if tag_eq_dec tag tag' then Some (with_binder b v m) else None
  | PAlias p' x =>
      match match_exn p' exn m with
      | Some m' => Some (imonad_local_env (EnvCons x (VExn exn)) m')
      | None => None
      end
  end.

Fixpoint match_eff (p : pattern) (b : binder) (eff : eff) (v : val) (m : imonad iresult) : option (imonad iresult) :=
  match p with
  | PAny => Some (with_binder b v m)
  | PVar x => Some (imonad_local_env (EnvCons x (VEff eff)) (with_binder b v m))
  | PConstr tag b' =>
      let (tag', v') := eff in
      if tag_eq_dec tag tag' then Some (with_binder b' v' (with_binder b v m)) else None
  | PAlias p' x =>
      match match_eff p' b eff v m with
      | Some m' => Some (imonad_local_env (EnvCons x (VEff eff)) m')
      | None => None
      end
  end.

Definition interpreter : Type := kont -> term -> imonad iresult.

Definition interpret_term1_with (self : interpreter) (k : kont) (t : term1) (v : val) : imonad iresult :=
  let (b, t') := t in with_binder b v (self k t').

Definition interpret_term2_with (self : interpreter) (k : kont) (t : term2) (v1 v2 : val) : imonad iresult :=
  let (b1, b2, t') := t in with_binder b1 v1 (with_binder b2 v2 (self k t')).

Definition interpret_clo1_with (self : interpreter) (k : kont) (c : clo1) (v : val) : imonad iresult :=
  let (env, t) := c in imonad_use_env env (interpret_term1_with self k t v).

Definition interpret_clo2_with (self : interpreter) (k : kont) (c : clo2) (v1 v2 : val) : imonad iresult :=
  let (env, t) := c in imonad_use_env env (interpret_term2_with self k t v1 v2).

Definition interpret_ctx_clo_with (self : interpreter) (k : kont) (c : ctx_clo) (v : val) : imonad iresult :=
  match c with
  | CCtx0 env t => imonad_use_env env (self k t)
  | CCtx1 env t => imonad_use_env env (interpret_term1_with self k t v)
  end.

Definition interpret_kont_with (self : interpreter) (k : kont) (v : val) : imonad iresult :=
  match k with
  | KNil => imonad_pure (RReturn v)
  | KCons c k' => interpret_ctx_clo_with self k' c v
  end.

Definition interpret_ret_term_with (self : interpreter) (k : kont) (t : ret_term) (v : val) : imonad iresult :=
  match t with
  | TRet0 => interpret_kont_with self k v
  | TRet1 b t' => with_binder b v (self k t')
  end.

Fixpoint interpret_exn_term_with (self : interpreter) (k : kont) (t : exn_term) (exn : exn) : option (imonad iresult) :=
  match t with
  | TExnBase p t' => match_exn p exn (self k t')
  | TExnCons p t1 t2 =>
      match match_exn p exn (self k t1) with
      | Some _ as r => r
      | None => interpret_exn_term_with self k t2 exn
      end
  end.

Fixpoint interpret_eff_term_with (self : interpreter) (k : kont) (t : eff_term) (eff : eff) (v : val) : option (imonad iresult) :=
  match t with
  | TEffBase p b t' => match_eff p b eff v (self k t')
  | TEffCons p b t1 t2 =>
      match match_eff p b eff v (self k t1) with
      | Some _ as r => r
      | None => interpret_eff_term_with self k t2 eff v
      end
  end.

Definition interpret_try_clo_with (self : interpreter) (k : kont) (c : try_clo) (r : iresult) : imonad iresult :=
  match r with
  | RReturn v => interpret_kont_with self k v
  | RShift tag f mk => imonad_pure (RShift tag f (MKTry mk c k))
  | RControl tag f mk => imonad_pure (RControl tag f (MKTry mk c k))
  | RRaise exn =>
      let (env, t) := c in
      match interpret_exn_term_with self k t exn with
      | Some m => imonad_use_env env m
      | None => imonad_pure r
      end
  | RPerform eff mk => imonad_pure (RPerform eff (MKTry mk c k))
  end.

Definition interpret_handle_clo_with (self : interpreter) (k : kont) (c : handle_clo) (r : iresult) : imonad iresult :=
  match r with
  | RReturn v => let (env, t, _) := c in imonad_use_env env (interpret_ret_term_with self k t v)
  | RShift tag f mk => imonad_pure (RShift tag f (MKHandle mk c k))
  | RControl tag f mk => imonad_pure (RControl tag f (MKHandle mk c k))
  | RRaise _ => imonad_pure r
  | RPerform eff mk =>
      let (env, _, t) := c in
      match interpret_eff_term_with self k t eff (VKontHandle mk c) with
      | Some m => imonad_use_env env m
      | None => imonad_pure (RPerform eff (MKHandle mk c k))
      end
  end.

Definition interpret_shallow_handle_clo_with (self : interpreter) (k : kont) (c : handle_clo) (r : iresult) : imonad iresult :=
  match r with
  | RReturn v => let (env, t, _) := c in imonad_use_env env (interpret_ret_term_with self k t v)
  | RShift tag f mk => imonad_pure (RShift tag f (MKShallowHandle mk c k))
  | RControl tag f mk => imonad_pure (RControl tag f (MKShallowHandle mk c k))
  | RRaise _ => imonad_pure r
  | RPerform eff mk =>
      let (env, _, t) := c in
      match interpret_eff_term_with self k t eff (VKont mk) with
      | Some m => imonad_use_env env m
      | None => imonad_pure (RPerform eff (MKShallowHandle mk c k))
      end
  end.

Fixpoint interpret_metakont_with (self : interpreter) (mk : metakont) (v : val) : imonad iresult :=
  match mk with
  | MKPure k => interpret_kont_with self k v
  | MKReset mk' tag k => interpret_reset k tag (interpret_metakont_with self mk' v) (interpret_kont_with self k)
  | MKPrompt mk' tag k => interpret_prompt k tag (interpret_metakont_with self mk' v) (interpret_kont_with self k)
  | MKTry mk' c k => interpret_metakont_with self mk' v >>= interpret_try_clo_with self k c
  | MKHandle mk' c k => interpret_metakont_with self mk' v >>= interpret_handle_clo_with self k c
  | MKShallowHandle mk' c k => interpret_metakont_with self mk' v >>= interpret_shallow_handle_clo_with self k c
  end.

Definition interpret_app (self : interpreter) (k : kont) (m1 m2 : imonad val) (f : val -> imonad iresult) : imonad iresult :=
  v <- m1;
  match v with
  | VFun c => m2 >>= interpret_clo1_with self k c
  | VFix c => m2 >>= interpret_clo2_with self k c v
  | VKontReset mk tag => interpret_reset k tag (m2 >>= interpret_metakont_with self mk) f
  | VKont mk => m2 >>= interpret_metakont_with self (metakont_extend mk k)
  | VKontHandle mk c => m2 >>= interpret_metakont_with self mk >>= interpret_handle_clo_with self k c
  | _ => imonad_throw (TypeError "")
  end.

Set Implicit Arguments.

Inductive term_graph : kont -> term -> Prop :=
| GTVal k t' : kont_graph k -> term_graph k (TVal t')
| GTApp k t1 t2 : kont_graph k -> term_graph k (TApp t1 t2)
| GTLet k t1 t2 : (forall env, term_graph (KCons (CCtx1 env t2) k) t1) -> term_graph k (TLet t1 t2)
| GTSeq k t1 t2 : (forall env, term_graph (KCons (CCtx0 env t2) k) t1) -> term_graph k (TSeq t1 t2)
| GTIf k t1 t2 t3 : term_graph k t2 -> term_graph k t3 -> term_graph k (TIf t1 t2 t3)
| GTSplit k t1 t2 : term2_graph k t2 -> term_graph k (TSplit t1 t2)
| GTCase k t1 t2 t3 : term1_graph k t2 -> term1_graph k t3 -> term_graph k (TCase t1 t2 t3)
| GTShift k tag t' : (forall env, ctx_clo_graph KNil (CCtx1 env t')) -> term_graph k (TShift tag t')
| GTReset k tag t' : term_graph KNil t' -> kont_graph k -> term_graph k (TReset tag t')
| GTControl k tag t' : (forall env, ctx_clo_graph KNil (CCtx1 env t')) -> term_graph k (TControl tag t')
| GTPrompt k tag t' : term_graph KNil t' -> kont_graph k -> term_graph k (TPrompt tag t')
| GTRaise k t' : term_graph k (TRaise t')
| GTTry k t1 t2 : term_graph KNil t1 -> kont_graph k -> exn_term_graph k t2 -> term_graph k (TTry t1 t2)
| GTPerform k t' : term_graph k (TPerform t')
| GTHandle k t1 t2 t3 : term_graph KNil t1 -> ret_term_graph k t2 -> eff_term_graph k t3 -> term_graph k (THandle t1 t2 t3)
| GTShallowHandle k t1 t2 t3 : term_graph KNil t1 -> ret_term_graph k t2 -> eff_term_graph k t3 -> term_graph k (TShallowHandle t1 t2 t3)
with term1_graph : kont -> term1 -> Prop :=
| GT1 k b t' : term_graph k t' -> term1_graph k (T1 b t')
with term2_graph : kont -> term2 -> Prop :=
| GT2 k b1 b2 t' : term_graph k t' -> term2_graph k (T2 b1 b2 t')
with ret_term_graph : kont -> ret_term -> Prop :=
| GTRet0 k : kont_graph k -> ret_term_graph k TRet0
| GTRet1 k b t' : term_graph k t' -> ret_term_graph k (TRet1 b t')
with exn_term_graph : kont -> exn_term -> Prop :=
| GTExnBase k p t' : term_graph k t' -> exn_term_graph k (TExnBase p t')
| GTExnCons k p t1 t2 : term_graph k t1 -> exn_term_graph k t2 -> exn_term_graph k (TExnCons p t1 t2)
with eff_term_graph : kont -> eff_term -> Prop :=
| GTEffBase k p b t' : term_graph k t' -> eff_term_graph k (TEffBase p b t')
| GTEffCons k p b t1 t2 : term_graph k t1 -> eff_term_graph k t2 -> eff_term_graph k (TEffCons p b t1 t2)
with ctx_clo_graph : kont -> ctx_clo -> Prop :=
| GCCtx0 k env t : term_graph k t -> ctx_clo_graph k (CCtx0 env t)
| GCCtx1 k env t : term1_graph k t -> ctx_clo_graph k (CCtx1 env t)
with kont_graph : kont -> Prop :=
| GKNil : kont_graph KNil
| GKCons c k' : ctx_clo_graph k' c -> kont_graph (KCons c k').

Lemma GTVal_inv k t' : term_graph k (TVal t') -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTApp_inv k t1 t2 : term_graph k (TApp t1 t2) -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTLet_inv k t1 t2 : term_graph k (TLet t1 t2) -> forall env, term_graph (KCons (CCtx1 env t2) k) t1.
Proof. inversion 1; auto. Defined.

Lemma GTSeq_inv k t1 t2 : term_graph k (TSeq t1 t2) -> forall env, term_graph (KCons (CCtx0 env t2) k) t1.
Proof. inversion 1; auto. Defined.

Lemma GTIf_inv1 k t1 t2 t3 : term_graph k (TIf t1 t2 t3) -> term_graph k t2.
Proof. inversion 1; auto. Defined.

Lemma GTIf_inv2 k t1 t2 t3 : term_graph k (TIf t1 t2 t3) -> term_graph k t3.
Proof. inversion 1; auto. Defined.

Lemma GTSplit_inv k t1 t2 : term_graph k (TSplit t1 t2) -> term2_graph k t2.
Proof. inversion 1; auto. Defined.

Lemma GTCase_inv1 k t1 t2 t3 : term_graph k (TCase t1 t2 t3) -> term1_graph k t2.
Proof. inversion 1; auto. Defined.

Lemma GTCase_inv2 k t1 t2 t3 : term_graph k (TCase t1 t2 t3) -> term1_graph k t3.
Proof. inversion 1; auto. Defined.

Lemma GTShift_inv k tag t' : term_graph k (TShift tag t') -> forall env, ctx_clo_graph KNil (CCtx1 env t').
Proof. inversion 1; auto. Defined.

Lemma GTReset_inv1 k tag t' : term_graph k (TReset tag t') -> term_graph KNil t'.
Proof. inversion 1; auto. Defined.

Lemma GTReset_inv2 k tag t' : term_graph k (TReset tag t') -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTControl_inv k tag t' : term_graph k (TControl tag t') -> forall env, ctx_clo_graph KNil (CCtx1 env t').
Proof. inversion 1; auto. Defined.

Lemma GTPrompt_inv1 k tag t' : term_graph k (TPrompt tag t') -> term_graph KNil t'.
Proof. inversion 1; auto. Defined.

Lemma GTPrompt_inv2 k tag t' : term_graph k (TPrompt tag t') -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTTry_inv1 k t1 t2 : term_graph k (TTry t1 t2) -> term_graph KNil t1.
Proof. inversion 1; auto. Defined.

Lemma GTTry_inv2 k t1 t2 : term_graph k (TTry t1 t2) -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTTry_inv3 k t1 t2 : term_graph k (TTry t1 t2) -> exn_term_graph k t2.
Proof. inversion 1; auto. Defined.

Lemma GTHandle_inv1 k t1 t2 t3 : term_graph k (THandle t1 t2 t3) -> term_graph KNil t1.
Proof. inversion 1; auto. Defined.

Lemma GTHandle_inv2 k t1 t2 t3 : term_graph k (THandle t1 t2 t3) -> ret_term_graph k t2.
Proof. inversion 1; auto. Defined.

Lemma GTHandle_inv3 k t1 t2 t3 : term_graph k (THandle t1 t2 t3) -> eff_term_graph k t3.
Proof. inversion 1; auto. Defined.

Lemma GTShallowHandle_inv1 k t1 t2 t3 : term_graph k (TShallowHandle t1 t2 t3) -> term_graph KNil t1.
Proof. inversion 1; auto. Defined.

Lemma GTShallowHandle_inv2 k t1 t2 t3 : term_graph k (TShallowHandle t1 t2 t3) -> ret_term_graph k t2.
Proof. inversion 1; auto. Defined.

Lemma GTShallowHandle_inv3 k t1 t2 t3 : term_graph k (TShallowHandle t1 t2 t3) -> eff_term_graph k t3.
Proof. inversion 1; auto. Defined.

Lemma GT1_inv k b t' : term1_graph k (T1 b t') -> term_graph k t'.
Proof. inversion 1; auto. Defined.

Lemma GT2_inv k b1 b2 t' : term2_graph k (T2 b1 b2 t') -> term_graph k t'.
Proof. inversion 1; auto. Defined.

Lemma GTRet0_inv k : ret_term_graph k TRet0 -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTRet1_inv k b t' : ret_term_graph k (TRet1 b t') -> term_graph k t'.
Proof. inversion 1; auto. Defined.

Lemma GTExnBase_inv k p t' : exn_term_graph k (TExnBase p t') -> term_graph k t'.
Proof. inversion 1; auto. Defined.

Lemma GTExnCons_inv1 k p t1 t2 : exn_term_graph k (TExnCons p t1 t2) -> term_graph k t1.
Proof. inversion 1; auto. Defined.

Lemma GTExnCons_inv2 k p t1 t2 : exn_term_graph k (TExnCons p t1 t2) -> exn_term_graph k t2.
Proof. inversion 1; auto. Defined.

Lemma GTEffBase_inv k p b t' : eff_term_graph k (TEffBase p b t') -> term_graph k t'.
Proof. inversion 1; auto. Defined.

Lemma GTEffCons_inv1 k p b t1 t2 : eff_term_graph k (TEffCons p b t1 t2) -> term_graph k t1.
Proof. inversion 1; auto. Defined.

Lemma GTEffCons_inv2 k p b t1 t2 : eff_term_graph k (TEffCons p b t1 t2) -> eff_term_graph k t2.
Proof. inversion 1; auto. Defined.

Lemma GCCtx0_inv k env t : ctx_clo_graph k (CCtx0 env t) -> term_graph k t.
Proof. inversion 1; auto. Defined.

Lemma GCCtx1_inv k env t : ctx_clo_graph k (CCtx1 env t) -> term1_graph k t.
Proof. inversion 1; auto. Defined.

Lemma GKCons_inv c k' : kont_graph (KCons c k') -> ctx_clo_graph k' c.
Proof. inversion 1; auto. Defined.

Fixpoint build_term_graph_dep (k : kont) (G : kont_graph k) (t : term) : term_graph k t :=
  match t with
  | TVal t' => GTVal t' G
  | TApp t1 t2 => GTApp t1 t2 G
  | TLet t1 t2 => GTLet (fun env => build_term_graph_dep (GKCons (GCCtx1 env (build_term1_graph_dep G t2))) t1)
  | TSeq t1 t2 => GTSeq (fun env => build_term_graph_dep (GKCons (GCCtx0 env (build_term_graph_dep G t2))) t1)
  | TIf t1 t2 t3 => GTIf t1 (build_term_graph_dep G t2) (build_term_graph_dep G t3)
  | TSplit t1 t2 => GTSplit t1 (build_term2_graph_dep G t2)
  | TCase t1 t2 t3 => GTCase t1 (build_term1_graph_dep G t2) (build_term1_graph_dep G t3)
  | TShift tag t' => GTShift k tag (fun env => GCCtx1 env (build_term1_graph_dep GKNil t'))
  | TReset tag t' => GTReset tag (build_term_graph_dep GKNil t') G
  | TControl tag t' => GTControl k tag (fun env => GCCtx1 env (build_term1_graph_dep GKNil t'))
  | TPrompt tag t' => GTPrompt tag (build_term_graph_dep GKNil t') G
  | TRaise t' => GTRaise k t'
  | TTry t1 t2 => GTTry (build_term_graph_dep GKNil t1) G (build_exn_term_graph_dep G t2)
  | TPerform t' => GTPerform k t'
  | THandle t1 t2 t3 => GTHandle (build_term_graph_dep GKNil t1) (build_ret_term_graph_dep G t2) (build_eff_term_graph_dep G t3)
  | TShallowHandle t1 t2 t3 => GTShallowHandle (build_term_graph_dep GKNil t1) (build_ret_term_graph_dep G t2) (build_eff_term_graph_dep G t3)
  end
with build_term1_graph_dep (k : kont) (G : kont_graph k) (t : term1) : term1_graph k t :=
  match t with
  | T1 b t' => GT1 b (build_term_graph_dep G t')
  end
with build_term2_graph_dep (k : kont) (G : kont_graph k) (t : term2) : term2_graph k t :=
  match t with
  | T2 b1 b2 t' => GT2 b1 b2 (build_term_graph_dep G t')
  end
with build_ret_term_graph_dep (k : kont) (G : kont_graph k) (t : ret_term) : ret_term_graph k t :=
  match t with
  | TRet0 => GTRet0 G
  | TRet1 b t' => GTRet1 b (build_term_graph_dep G t')
  end
with build_exn_term_graph_dep (k : kont) (G : kont_graph k) (t : exn_term) : exn_term_graph k t :=
  match t with
  | TExnBase p t' => GTExnBase p (build_term_graph_dep G t')
  | TExnCons p t1 t2 => GTExnCons p (build_term_graph_dep G t1) (build_exn_term_graph_dep G t2)
  end
with build_eff_term_graph_dep (k : kont) (G : kont_graph k) (t : eff_term) : eff_term_graph k t :=
  match t with
  | TEffBase p b t' => GTEffBase p b (build_term_graph_dep G t')
  | TEffCons p b t1 t2 => GTEffCons p b (build_term_graph_dep G t1) (build_eff_term_graph_dep G t2)
  end.

Definition build_ctx_clo_graph_dep (k : kont) (G : kont_graph k) (c : ctx_clo) : ctx_clo_graph k c :=
  match c with
  | CCtx0 env t => GCCtx0 env (build_term_graph_dep G t)
  | CCtx1 env t => GCCtx1 env (build_term1_graph_dep G t)
  end.

Fixpoint interpret_term_dep (self : interpreter) (k : kont) (t : term) (G : term_graph k t) {struct G} : imonad iresult :=
  match t return term_graph k t -> imonad iresult with
  | TVal t' =>
      fun G => interpret_val_term t' >>= interpret_kont_dep self (GTVal_inv G)
  | TApp t1 t2 =>
      fun G => interpret_app self k
                 (interpret_val_term t1)
                 (interpret_val_term t2)
                 (interpret_kont_dep self (GTApp_inv G))
  | TLet t1 t2 =>
      fun G => interpret_let (fun env => interpret_term_dep self (GTLet_inv G env))
  | TSeq t1 t2 =>
      fun G => interpret_seq (fun env => interpret_term_dep self (GTSeq_inv G env))
  | TIf t1 t2 t3 =>
      fun G => interpret_if
                 (interpret_val_term t1)
                 (interpret_term_dep self (GTIf_inv1 G))
                 (interpret_term_dep self (GTIf_inv2 G))
  | TSplit t1 t2 =>
      fun G => interpret_split
                 (interpret_val_term t1)
                 (interpret_term2_dep self (GTSplit_inv G))
  | TCase t1 t2 t3 =>
      fun G => interpret_case
                 (interpret_val_term t1)
                 (interpret_term1_dep self (GTCase_inv1 G))
                 (interpret_term1_dep self (GTCase_inv2 G))
  | TShift tag t' =>
      fun G => interpret_shift k tag (fun env => interpret_ctx_clo_dep self (GTShift_inv G env))
  | TReset tag t' =>
      fun G => interpret_reset k tag
                 (interpret_term_dep self (GTReset_inv1 G))
                 (interpret_kont_dep self (GTReset_inv2 G))
  | TControl tag t' =>
      fun G => interpret_control k tag (fun env => interpret_ctx_clo_dep self (GTControl_inv G env))
  | TPrompt tag t' =>
      fun G => interpret_prompt k tag
                 (interpret_term_dep self (GTPrompt_inv1 G))
                 (interpret_kont_dep self (GTPrompt_inv2 G))
  | TRaise t' =>
      fun G => interpret_raise (interpret_val_term t')
  | TTry t1 t2 =>
      fun G => interpret_try k t2
                 (interpret_term_dep self (GTTry_inv1 G))
                 (interpret_kont_dep self (GTTry_inv2 G))
                 (interpret_exn_term_dep self (GTTry_inv3 G))
  | TPerform t' =>
      fun G => interpret_perform k (interpret_val_term t')
  | THandle t1 t2 t3 =>
      fun G => interpret_handle k t2 t3
                 (interpret_term_dep self (GTHandle_inv1 G))
                 (interpret_ret_term_dep self (GTHandle_inv2 G))
                 (interpret_eff_term_dep self (GTHandle_inv3 G))
  | TShallowHandle t1 t2 t3 =>
      fun G => interpret_shallow_handle k t2 t3
                 (interpret_term_dep self (GTShallowHandle_inv1 G))
                 (interpret_ret_term_dep self (GTShallowHandle_inv2 G))
                 (interpret_eff_term_dep self (GTShallowHandle_inv3 G))
  end G
with interpret_term1_dep (self : interpreter) (k : kont) (t : term1) (G : term1_graph k t) (v : val) {struct G} : imonad iresult :=
  match t return term1_graph k t -> imonad iresult with
  | T1 b t' => fun G => with_binder b v (interpret_term_dep self (GT1_inv G))
  end G
with interpret_term2_dep (self : interpreter) (k : kont) (t : term2) (G : term2_graph k t) (v1 v2 : val) {struct G} : imonad iresult :=
  match t return term2_graph k t -> imonad iresult with
  | T2 b1 b2 t' => fun G => with_binder b1 v1 (with_binder b2 v2 (interpret_term_dep self (GT2_inv G)))
  end G
with interpret_ret_term_dep (self : interpreter) (k : kont) (t : ret_term) (G : ret_term_graph k t) (v : val) {struct G} : imonad iresult :=
  match t return ret_term_graph k t -> imonad iresult with
  | TRet0 => fun G => interpret_kont_dep self (GTRet0_inv G) v
  | TRet1 b t' => fun G => with_binder b v (interpret_term_dep self (GTRet1_inv G))
  end G
with interpret_exn_term_dep (self : interpreter) (k : kont) (t : exn_term) (G : exn_term_graph k t) (exn : exn) {struct G} :
  option (imonad iresult) :=
  match t return exn_term_graph k t -> option (imonad iresult) with
  | TExnBase p t' =>
      fun G => match_exn p exn (interpret_term_dep self (GTExnBase_inv G))
  | TExnCons p t1 t2 =>
      fun G => match match_exn p exn (interpret_term_dep self (GTExnCons_inv1 G)) with
               | Some _ as r => r
               | None => interpret_exn_term_dep self (GTExnCons_inv2 G) exn
               end
  end G
with interpret_eff_term_dep (self : interpreter) (k : kont) (t : eff_term) (G : eff_term_graph k t) (eff : eff) (v : val) {struct G} :
  option (imonad iresult) :=
  match t return eff_term_graph k t -> option (imonad iresult) with
  | TEffBase p b t' =>
      fun G => match_eff p b eff v (interpret_term_dep self (GTEffBase_inv G))
  | TEffCons p b t1 t2 =>
      fun G => match match_eff p b eff v (interpret_term_dep self (GTEffCons_inv1 G)) with
               | Some _ as r => r
               | None => interpret_eff_term_dep self (GTEffCons_inv2 G) eff v
               end
  end G
with interpret_ctx_clo_dep (self : interpreter) (k : kont) (c : ctx_clo) (G : ctx_clo_graph k c) (v : val) {struct G} : imonad iresult :=
  match c return ctx_clo_graph k c -> imonad iresult with
  | CCtx0 env t => fun G => imonad_use_env env (interpret_term_dep self (GCCtx0_inv G))
  | CCtx1 env t => fun G => imonad_use_env env (interpret_term1_dep self (GCCtx1_inv G) v)
  end G
with interpret_kont_dep (self : interpreter) (k : kont) (G : kont_graph k) (v : val) {struct G} : imonad iresult :=
  match k return kont_graph k -> imonad iresult with
  | KNil => fun G => imonad_pure (RReturn v)
  | KCons c k' => fun G => interpret_ctx_clo_dep self (GKCons_inv G) v
  end G.

Unset Implicit Arguments.

Fixpoint build_kont_graph (k : kont) : kont_graph k :=
  match k with
  | KNil => GKNil
  | KCons c k' => GKCons (build_ctx_clo_graph_dep (build_kont_graph k') c)
  end.

Definition build_term_graph (k : kont) (t : term) : term_graph k t :=
  build_term_graph_dep (build_kont_graph k) t.

Definition interpret_term_aux (self : interpreter) (k : kont) (t : term) : imonad iresult :=
  interpret_term_dep self (build_term_graph k t).

Fixpoint interpret_term (fuel : nat) (k : kont) (t : term) : imonad iresult :=
  match fuel with
  | O => imonad_throw OutOfFuel
  | S fuel' => interpret_term_aux (interpret_term fuel') k t
  end.

Definition run_term (fuel : nat) (t : term) : (ierror + val) * iheap :=
  imonad_run (interpret_term fuel KNil t >>= unwrap_RReturn) EnvNil iheap_empty.

Definition eval_term (fuel : nat) (t : term) : ierror + val :=
  fst (run_term fuel t).

Definition exec_term (fuel : nat) (t : term) : iheap :=
  snd (run_term fuel t).
