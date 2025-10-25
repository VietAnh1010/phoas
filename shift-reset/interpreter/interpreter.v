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

Fixpoint delimit_reset (tag : tag) (r : iresult) : imonad iresult :=
  match r with
  | RShift mk f tag' => if tag_eqb tag tag' then f (VMKReset mk tag) >>= delimit_reset tag else imonad_pure r
  | _ => imonad_pure r
  end.

Fixpoint delimit_prompt (tag : tag) (r : iresult) : imonad iresult :=
  match r with
  | RControl mk f tag' => if tag_eqb tag tag' then f (VMKPure mk) >>= delimit_prompt tag else imonad_pure r
  | _ => imonad_pure r
  end.

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

Definition interpreter : Type := kont -> term -> imonad iresult.

Definition interpret_term1_with (self : interpreter) (k : kont) (t : term1) (v : val) : imonad iresult :=
  let (b, t') := t in with_binder b v (self k t').

Definition interpret_term2_with (self : interpreter) (k : kont) (t : term2) (v1 v2 : val) : imonad iresult :=
  let (b1, b2, t') := t in with_binder2 b1 b2 v1 v2 (self k t').

Definition interpret_kont_clo_with (self : interpreter) (k : kont) (c : kont_clo) (v : val) : imonad iresult :=
  match c with
  | CKSeq env t => imonad_use_env env (self k t)
  | CKLet env t => imonad_use_env env (interpret_term1_with self k t v)
  end.

Definition interpret_kont_with (self : interpreter) (k : kont) (v : val) : imonad iresult :=
  match k with
  | KNil => imonad_pure (RVal v)
  | KCons c k' => interpret_kont_clo_with self k' c v
  end.

Definition interpret_ret_term_with (self : interpreter) (k : kont) (t : ret_term) (v : val) : imonad iresult :=
  match t with
  | TRetNone => interpret_kont_with self k v
  | TRetSome b t' => with_binder b v (self k t')
  end.

Fixpoint interpret_exn_term_with (self : interpreter) (k : kont) (t : exn_term) (exn : exn) : option (imonad iresult) :=
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

Fixpoint interpret_eff_term_with (self : interpreter) (k : kont) (t : eff_term) (eff : eff) (v : val) : option (imonad iresult) :=
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

Fixpoint interpret_metakont_with (self : interpreter) (mk : metakont) (v : val) : imonad iresult :=
  match mk with
  | MKPure k => interpret_kont_with self k v
  | MKReset mk' tag k =>
      r <- interpret_metakont_with self mk' v;
      r <- delimit_reset tag r;
      match r with
      | RVal v => interpret_kont_with self k v
      | RShift mk f tag' => imonad_pure (RShift (MKReset mk tag k) f tag')
      | RControl mk f tag' => imonad_pure (RControl (MKReset mk tag k) f tag')
      | RRaise _ => imonad_pure r
      | RPerform mk eff => imonad_pure (RPerform (MKReset mk tag k) eff)
      end
  | MKPrompt mk' tag k =>
      r <- interpret_metakont_with self mk' v;
      r <- delimit_prompt tag r;
      match r with
      | RVal v => interpret_kont_with self k v
      | RShift mk f tag' => imonad_pure (RShift (MKPrompt mk tag k) f tag')
      | RControl mk f tag' => imonad_pure (RControl (MKPrompt mk tag k) f tag')
      | RRaise _ => imonad_pure r
      | RPerform mk eff => imonad_pure (RPerform (MKPrompt mk tag k) eff)
      end
  | MKTry mk' c k =>
      r <- interpret_metakont_with self mk' v;
      match r with
      | RVal v => interpret_kont_with self k v
      | RShift mk f tag => imonad_pure (RShift (MKTry mk c k) f tag)
      | RControl mk f tag => imonad_pure (RControl (MKTry mk c k) f tag)
      | RRaise exn =>
          let (env, t) := c in
          match interpret_exn_term_with self k t exn with
          | Some m => imonad_use_env env m
          | None => imonad_pure r
          end
      | RPerform mk eff => imonad_pure (RPerform (MKTry mk c k) eff)
      end
  | MKHandle mk' c k =>
      r <- interpret_metakont_with self mk' v;
      match r with
      | RVal v => let (env, t, _) := c in imonad_use_env env (interpret_ret_term_with self k t v)
      | RShift mk f tag => imonad_pure (RShift (MKHandle mk c k) f tag)
      | RControl mk f tag => imonad_pure (RControl (MKHandle mk c k) f tag)
      | RRaise _ => imonad_pure r
      | RPerform mk eff =>
          let (env, _, t) := c in
          match interpret_eff_term_with self k t eff (VMKHandle mk c) with
          | Some m => imonad_use_env env m
          | None => imonad_pure (RPerform (MKHandle mk c k) eff)
          end
      end
  | MKShallowHandle mk' c k =>
      r <- interpret_metakont_with self mk' v;
      match r with
      | RVal v => let (env, t, _) := c in imonad_use_env env (interpret_ret_term_with self k t v)
      | RShift mk f tag => imonad_pure (RShift (MKShallowHandle mk c k) f tag)
      | RControl mk f tag => imonad_pure (RControl (MKShallowHandle mk c k) f tag)
      | RRaise _ => imonad_pure r
      | RPerform mk eff =>
          let (env, _, t) := c in
          match interpret_eff_term_with self k t eff (VMKPure mk) with
          | Some m => imonad_use_env env m
          | None => imonad_pure (RPerform (MKShallowHandle mk c k) eff)
          end
      end
  end.

Set Implicit Arguments.

Inductive term_graph : kont -> term -> Prop :=
| GTVal k t' : kont_graph k -> term_graph k (TVal t')
| GTApp k t1 t2 : term_graph k (TApp t1 t2)
| GTSeq k t1 t2 : (forall env, term_graph (KCons (CKSeq env t2) k) t1) -> term_graph k (TSeq t1 t2)
| GTLet k t1 t2 : (forall env, term_graph (KCons (CKLet env t2) k) t1) -> term_graph k (TLet t1 t2)
| GTIf k t1 t2 t3 : term_graph k t2 -> term_graph k t3 -> term_graph k (TIf t1 t2 t3)
| GTSplit k t1 t2 : term2_graph k t2 -> term_graph k (TSplit t1 t2)
| GTCase k t1 t2 t3 : term1_graph k t2 -> term1_graph k t3 -> term_graph k (TCase t1 t2 t3)
| GTShift k tag t' : term1_graph KNil t' -> term_graph k (TShift tag t')
| GTReset k tag t' : term_graph KNil t' -> kont_graph k -> term_graph k (TReset tag t')
| GTControl k tag t' : term1_graph KNil t' -> term_graph k (TControl tag t')
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
| GTRetNone k : kont_graph k -> ret_term_graph k TRetNone
| GTRetSome k b t' : term_graph k t' -> ret_term_graph k (TRetSome b t')
with exn_term_graph : kont -> exn_term -> Prop :=
| GTExnLast k p t' : term_graph k t' -> exn_term_graph k (TExnLast p t')
| GTExnCons k p t1 t2 : term_graph k t1 -> exn_term_graph k t2 -> exn_term_graph k (TExnCons p t1 t2)
with eff_term_graph : kont -> eff_term -> Prop :=
| GTEffLast k p b t' : term_graph k t' -> eff_term_graph k (TEffLast p b t')
| GTEffCons k p b t1 t2 : term_graph k t1 -> eff_term_graph k t2 -> eff_term_graph k (TEffCons p b t1 t2)
with kont_clo_graph : kont -> kont_clo -> Prop :=
| GCKSeq k env t : term_graph k t -> kont_clo_graph k (CKSeq env t)
| GCKLet k env t : term1_graph k t -> kont_clo_graph k (CKLet env t)
with kont_graph : kont -> Prop :=
| GKNil : kont_graph KNil
| GKCons c k' : kont_clo_graph k' c -> kont_graph (KCons c k').

Lemma GTVal_inv k t' : term_graph k (TVal t') -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTSeq_inv k t1 t2 : term_graph k (TSeq t1 t2) -> forall env, term_graph (KCons (CKSeq env t2) k) t1.
Proof. inversion 1; auto. Defined.

Lemma GTLet_inv k t1 t2 : term_graph k (TLet t1 t2) -> forall env, term_graph (KCons (CKLet env t2) k) t1.
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

Lemma GTShift_inv k tag t' : term_graph k (TShift tag t') -> term1_graph KNil t'.
Proof. inversion 1; auto. Defined.

Lemma GTReset_inv1 k tag t' : term_graph k (TReset tag t') -> term_graph KNil t'.
Proof. inversion 1; auto. Defined.

Lemma GTReset_inv2 k tag t' : term_graph k (TReset tag t') -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTControl_inv k tag t' : term_graph k (TControl tag t') -> term1_graph KNil t'.
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

Lemma GTRetNone_inv k : ret_term_graph k TRetNone -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTRetSome_inv k b t' : ret_term_graph k (TRetSome b t') -> term_graph k t'.
Proof. inversion 1; auto. Defined.

Lemma GTExnLast_inv k p t' : exn_term_graph k (TExnLast p t') -> term_graph k t'.
Proof. inversion 1; auto. Defined.

Lemma GTExnCons_inv1 k p t1 t2 : exn_term_graph k (TExnCons p t1 t2) -> term_graph k t1.
Proof. inversion 1; auto. Defined.

Lemma GTExnCons_inv2 k p t1 t2 : exn_term_graph k (TExnCons p t1 t2) -> exn_term_graph k t2.
Proof. inversion 1; auto. Defined.

Lemma GTEffLast_inv k p b t' : eff_term_graph k (TEffLast p b t') -> term_graph k t'.
Proof. inversion 1; auto. Defined.

Lemma GTEffCons_inv1 k p b t1 t2 : eff_term_graph k (TEffCons p b t1 t2) -> term_graph k t1.
Proof. inversion 1; auto. Defined.

Lemma GTEffCons_inv2 k p b t1 t2 : eff_term_graph k (TEffCons p b t1 t2) -> eff_term_graph k t2.
Proof. inversion 1; auto. Defined.

Lemma GCKSeq_inv k env t : kont_clo_graph k (CKSeq env t) -> term_graph k t.
Proof. inversion 1; auto. Defined.

Lemma GCKLet_inv k env t : kont_clo_graph k (CKLet env t) -> term1_graph k t.
Proof. inversion 1; auto. Defined.

Lemma GKCons_inv c k' : kont_graph (KCons c k') -> kont_clo_graph k' c.
Proof. inversion 1; auto. Defined.

Fixpoint build_term_graph_dep (k : kont) (G : kont_graph k) (t : term) : term_graph k t :=
  match t with
  | TVal t' => GTVal t' G
  | TApp t1 t2 => GTApp k t1 t2
  | TSeq t1 t2 => GTSeq (fun env => build_term_graph_dep (GKCons (GCKSeq env (build_term_graph_dep G t2))) t1)
  | TLet t1 t2 => GTLet (fun env => build_term_graph_dep (GKCons (GCKLet env (build_term1_graph_dep G t2))) t1)
  | TIf t1 t2 t3 => GTIf t1 (build_term_graph_dep G t2) (build_term_graph_dep G t3)
  | TSplit t1 t2 => GTSplit t1 (build_term2_graph_dep G t2)
  | TCase t1 t2 t3 => GTCase t1 (build_term1_graph_dep G t2) (build_term1_graph_dep G t3)
  | TShift tag t' => GTShift k tag (build_term1_graph_dep GKNil t')
  | TReset tag t' => GTReset tag (build_term_graph_dep GKNil t') G
  | TControl tag t' => GTControl k tag (build_term1_graph_dep GKNil t')
  | TPrompt tag t' => GTPrompt tag (build_term_graph_dep GKNil t') G
  | TRaise t' => GTRaise k t'
  | TTry t1 t2 => GTTry (build_term_graph_dep GKNil t1) G (build_exn_term_graph_dep G t2)
  | TPerform t' => GTPerform k t'
  | THandle t1 t2 t3 => GTHandle (build_term_graph_dep GKNil t1) (build_ret_term_graph_dep G t2) (build_eff_term_graph_dep G t3)
  | TShallowHandle t1 t2 t3 => GTShallowHandle (build_term_graph_dep GKNil t1) (build_ret_term_graph_dep G t2) (build_eff_term_graph_dep G t3)
  end
with build_term1_graph_dep (k : kont) (G : kont_graph k) (t : term1) : term1_graph k t :=
  let 'T1 b t' := t in GT1 b (build_term_graph_dep G t')
with build_term2_graph_dep (k : kont) (G : kont_graph k) (t : term2) : term2_graph k t :=
  let 'T2 b1 b2 t' := t in GT2 b1 b2 (build_term_graph_dep G t')
with build_ret_term_graph_dep (k : kont) (G : kont_graph k) (t : ret_term) : ret_term_graph k t :=
  match t with
  | TRetNone => GTRetNone G
  | TRetSome b t' => GTRetSome b (build_term_graph_dep G t')
  end
with build_exn_term_graph_dep (k : kont) (G : kont_graph k) (t : exn_term) : exn_term_graph k t :=
  match t with
  | TExnLast p t' => GTExnLast p (build_term_graph_dep G t')
  | TExnCons p t1 t2 => GTExnCons p (build_term_graph_dep G t1) (build_exn_term_graph_dep G t2)
  end
with build_eff_term_graph_dep (k : kont) (G : kont_graph k) (t : eff_term) : eff_term_graph k t :=
  match t with
  | TEffLast p b t' => GTEffLast p b (build_term_graph_dep G t')
  | TEffCons p b t1 t2 => GTEffCons p b (build_term_graph_dep G t1) (build_eff_term_graph_dep G t2)
  end.

Definition build_kont_clo_graph_dep (k : kont) (G : kont_graph k) (c : kont_clo) : kont_clo_graph k c :=
  match c with
  | CKSeq env t => GCKSeq env (build_term_graph_dep G t)
  | CKLet env t => GCKLet env (build_term1_graph_dep G t)
  end.

Fixpoint interpret_term_dep (self : interpreter) (k : kont) (t : term) (G : term_graph k t) {struct G} : imonad iresult :=
  match t return term_graph k t -> _ with
  | TVal t' => fun G => interpret_val_term t' >>= interpret_kont_dep self (GTVal_inv G)
  | TApp t1 t2 =>
      fun G =>
        u <- interpret_val_term t1;
        l <- unwrap_vlambda u;
        v <- interpret_val_term t2;
        match l with
        | LFun c => let (env, t) := c in imonad_use_env env (interpret_term1_with self k t v)
        | LFix c => let (env, t) := c in imonad_use_env env (interpret_term2_with self k t u v)
        | LMKPure mk => interpret_metakont_with self (metakont_extend mk k) v
        | LMKReset mk tag => interpret_metakont_with self (MKReset mk tag k) v
        | LMKHandle mk c => interpret_metakont_with self (MKHandle mk c k) v
        end
  | TSeq t1 t2 => fun G => env <- imonad_ask_env; interpret_term_dep self (GTSeq_inv G env)
  | TLet t1 t2 => fun G => env <- imonad_ask_env; interpret_term_dep self (GTLet_inv G env)
  | TIf t1 t2 t3 =>
      fun G =>
        v <- interpret_val_term t1;
        b <- unwrap_vbool v;
        if b then interpret_term_dep self (GTIf_inv1 G) else interpret_term_dep self (GTIf_inv2 G)
  | TSplit t1 t2 =>
      fun G =>
        v <- interpret_val_term t1;
        p <- unwrap_vprod v;
        let (v1, v2) := p in interpret_term2_dep self (GTSplit_inv G) v1 v2
  | TCase t1 t2 t3 =>
      fun G =>
        v <- interpret_val_term t1;
        s <- unwrap_vsum v;
        match s with
        | inl v' => interpret_term1_dep self (GTCase_inv1 G) v'
        | inr v' => interpret_term1_dep self (GTCase_inv2 G) v'
        end
  | TShift tag t' =>
      fun G =>
        imonad_asks_env (fun env => RShift (MKPure k) (fun v => imonad_use_env env (interpret_term1_dep self (GTShift_inv G) v)) tag)
  | TReset tag t' =>
      fun G =>
        r <- interpret_term_dep self (GTReset_inv1 G);
        r <- delimit_reset tag r;
        match r with
        | RVal v => interpret_kont_dep self (GTReset_inv2 G) v
        | RShift mk f tag' => imonad_pure (RShift (MKReset mk tag k) f tag')
        | RControl mk f tag' => imonad_pure (RControl (MKReset mk tag k) f tag')
        | RRaise _ => imonad_pure r
        | RPerform mk eff => imonad_pure (RPerform (MKReset mk tag k) eff)
        end
  | TControl tag t' =>
      fun G =>
        imonad_asks_env (fun env => RControl (MKPure k) (fun v => imonad_use_env env (interpret_term1_dep self (GTControl_inv G) v)) tag)
  | TPrompt tag t' =>
      fun G =>
        r <- interpret_term_dep self (GTPrompt_inv1 G);
        r <- delimit_prompt tag r;
        match r with
        | RVal v => interpret_kont_dep self (GTPrompt_inv2 G) v
        | RShift mk f tag' => imonad_pure (RShift (MKPrompt mk tag k) f tag')
        | RControl mk f tag' => imonad_pure (RControl (MKPrompt mk tag k) f tag')
        | RRaise _ => imonad_pure r
        | RPerform mk eff => imonad_pure (RPerform (MKPrompt mk tag k) eff)
        end
  | TRaise t' => fun G => v <- interpret_val_term t'; RRaise <$> unwrap_vexn v
  | TTry t1 t2 =>
      fun G =>
        r <- interpret_term_dep self (GTTry_inv1 G);
        match r with
        | RVal v => interpret_kont_dep self (GTTry_inv2 G) v
        | RShift mk f tag => imonad_asks_env (fun env => RShift (MKTry' mk t2 k env) f tag)
        | RControl mk f tag => imonad_asks_env (fun env => RControl (MKTry' mk t2 k env) f tag)
        | RRaise exn =>
            match interpret_exn_term_dep self (GTTry_inv3 G) exn with
            | Some m => m
            | None => imonad_pure r
            end
        | RPerform mk eff => imonad_asks_env (fun env => RPerform (MKTry' mk t2 k env) eff)
        end
  | TPerform t' => fun G => v <- interpret_val_term t'; RPerform (MKPure k) <$> unwrap_veff v
  | THandle t1 t2 t3 =>
      fun G =>
        r <- interpret_term_dep self (GTHandle_inv1 G);
        match r with
        | RVal v => interpret_ret_term_dep self (GTHandle_inv2 G) v
        | RShift mk f tag => imonad_asks_env (fun env => RShift (MKHandle' mk t2 t3 k env) f tag)
        | RControl mk f tag => imonad_asks_env (fun env => RControl (MKHandle' mk t2 t3 k env) f tag)
        | RRaise _ => imonad_pure r
        | RPerform mk eff =>
            env <- imonad_ask_env;
            let c := CHandle env t2 t3 in
            match interpret_eff_term_dep self (GTHandle_inv3 G) eff (VMKHandle mk c) with
            | Some m => m
            | None => imonad_pure (RPerform (MKHandle mk c k) eff)
            end
        end
  | TShallowHandle t1 t2 t3 =>
      fun G =>
        r <- interpret_term_dep self (GTShallowHandle_inv1 G);
        match r with
        | RVal v => interpret_ret_term_dep self (GTShallowHandle_inv2 G) v
        | RShift mk f tag => imonad_asks_env (fun env => RShift (MKShallowHandle' mk t2 t3 k env) f tag)
        | RControl mk f tag => imonad_asks_env (fun env => RControl (MKShallowHandle' mk t2 t3 k env) f tag)
        | RRaise _ => imonad_pure r
        | RPerform mk eff =>
            match interpret_eff_term_dep self (GTShallowHandle_inv3 G) eff (VMKPure mk) with
            | Some m => m
            | None => imonad_asks_env (fun env => RPerform (MKShallowHandle' mk t2 t3 k env) eff)
            end
        end
  end G
with interpret_term1_dep (self : interpreter) (k : kont) (t : term1) (G : term1_graph k t) (v : val) {struct G} : imonad iresult :=
  (let 'T1 b t' := t return term1_graph k t -> _ in
   fun G => with_binder b v (interpret_term_dep self (GT1_inv G))) G
with interpret_term2_dep (self : interpreter) (k : kont) (t : term2) (G : term2_graph k t) (v1 v2 : val) {struct G} : imonad iresult :=
  (let 'T2 b1 b2 t' := t return term2_graph k t -> _ in
   fun G => with_binder2 b1 b2 v1 v2 (interpret_term_dep self (GT2_inv G))) G
with interpret_ret_term_dep (self : interpreter) (k : kont) (t : ret_term) (G : ret_term_graph k t) (v : val) {struct G} : imonad iresult :=
  match t return ret_term_graph k t -> _ with
  | TRetNone => fun G => interpret_kont_dep self (GTRetNone_inv G) v
  | TRetSome b t' => fun G => with_binder b v (interpret_term_dep self (GTRetSome_inv G))
  end G
with interpret_exn_term_dep (self : interpreter) (k : kont) (t : exn_term) (G : exn_term_graph k t) (exn : exn) {struct G} :
  option (imonad iresult) :=
  match t return exn_term_graph k t -> _ with
  | TExnLast p t' =>
      fun G =>
        match match_exn p exn with
        | Some f => Some (f (interpret_term_dep self (GTExnLast_inv G)))
        | None => None
        end
  | TExnCons p t1 t2 =>
      fun G =>
        match match_exn p exn with
        | Some f => Some (f (interpret_term_dep self (GTExnCons_inv1 G)))
        | None => interpret_exn_term_dep self (GTExnCons_inv2 G) exn
        end
  end G
with interpret_eff_term_dep (self : interpreter) (k : kont) (t : eff_term) (G : eff_term_graph k t) (eff : eff) (v : val) {struct G} :
  option (imonad iresult) :=
  match t return eff_term_graph k t -> _ with
  | TEffLast p b t' =>
      fun G =>
        match match_eff p b eff v with
        | Some f => Some (f (interpret_term_dep self (GTEffLast_inv G)))
        | None => None
        end
  | TEffCons p b t1 t2 =>
      fun G =>
        match match_eff p b eff v with
        | Some f => Some (f (interpret_term_dep self (GTEffCons_inv1 G)))
        | None => interpret_eff_term_dep self (GTEffCons_inv2 G) eff v
        end
  end G
with interpret_kont_clo_dep (self : interpreter) (k : kont) (c : kont_clo) (G : kont_clo_graph k c) (v : val) {struct G} : imonad iresult :=
  match c return kont_clo_graph k c -> _ with
  | CKSeq env t => fun G => imonad_use_env env (interpret_term_dep self (GCKSeq_inv G))
  | CKLet env t => fun G => imonad_use_env env (interpret_term1_dep self (GCKLet_inv G) v)
  end G
with interpret_kont_dep (self : interpreter) (k : kont) (G : kont_graph k) (v : val) {struct G} : imonad iresult :=
  match k return kont_graph k -> _ with
  | KNil => fun G => imonad_pure (RVal v)
  | KCons c k' => fun G => interpret_kont_clo_dep self (GKCons_inv G) v
  end G.

Unset Implicit Arguments.

Fixpoint build_kont_graph (k : kont) : kont_graph k :=
  match k with
  | KNil => GKNil
  | KCons c k' => GKCons (build_kont_clo_graph_dep (build_kont_graph k') c)
  end.

Definition build_term_graph (k : kont) (t : term) : term_graph k t :=
  build_term_graph_dep (build_kont_graph k) t.

Definition interpret_term_aux (self : interpreter) (k : kont) (t : term) : imonad iresult :=
  interpret_term_dep self (build_term_graph k t).

Fixpoint interpret_term (fuel : nat) (k : kont) (t : term) : imonad iresult :=
  match fuel with
  | O => imonad_throw_error Out_of_fuel
  | S fuel' => interpret_term_aux (interpret_term fuel') k t
  end.

Definition unwrap_rval (r : iresult) : imonad val :=
  match r with
  | RVal v => imonad_pure v
  | RShift _ _ tag => imonad_throw_error (Undelimited_shift tag)
  | RControl _ _ tag => imonad_throw_error (Undelimited_control tag)
  | RRaise exn => imonad_throw_error (Unhandled_exception exn)
  | RPerform _ eff => imonad_throw_error (Unhandled_effect eff)
  end.

Definition run_term (fuel : nat) (t : term) : (ierror + val) * iheap :=
  imonad_run (interpret_term fuel KNil t >>= unwrap_rval) EnvNil iheap_empty.

Definition eval_term (fuel : nat) (t : term) : ierror + val :=
  fst (run_term fuel t).

Definition exec_term (fuel : nat) (t : term) : iheap :=
  snd (run_term fuel t).
