From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax env kont loc tag var.
From shift_reset.interpreter Require Import ierror iheap imonad.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope imonad_scope.
Local Unset Elimination Schemes.

Inductive iresult : Type :=
| RReturn : val -> iresult
| RShift : (val -> imonad iresult) -> metakont -> iresult
| RControl : (val -> imonad iresult) -> metakont -> iresult
| RRaise : exn -> iresult.

Definition handle_RShift (r : iresult) : imonad iresult :=
  match r with
  | RShift f mk => f (VKontReset mk)
  | _ => imonad_pure r
  end.

Definition handle_RControl (r : iresult) : imonad iresult :=
  match r with
  | RControl f mk => f (VKont mk)
  | _ => imonad_pure r
  end.

Definition unwrap_RReturn (r : iresult) : imonad val :=
  match r with
  | RReturn v => imonad_pure v
  | RShift _ _ => imonad_throw (ControlError "undelimited shift")
  | RControl _ _ => imonad_throw (ControlError "undelimited control")
  | RRaise _ => imonad_throw (ControlError "unhandled exception")
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

Definition interpret_i2i (f : Z -> Z) (a : atom) : imonad val :=
  imonad_map (fun i => VInt (f i)) (interpret_atom a >>= unwrap_VInt).

Definition interpret_b2b (f : bool -> bool) (a : atom) : imonad val :=
  imonad_map (fun b => VBool (f b)) (interpret_atom a >>= unwrap_VBool).

Definition interpret_prim1 (p : prim1) : atom -> imonad val :=
  match p with
  | P1Neg => interpret_i2i Z.opp
  | P1Not => interpret_b2b negb
  end.

Definition interpret_ii2i (f : Z -> Z -> Z) (a1 a2 : atom) : imonad val :=
  imonad_lift2 (fun i1 i2 => VInt (f i1 i2)) (interpret_atom a1 >>= unwrap_VInt) (interpret_atom a2 >>= unwrap_VInt).

Definition interpret_ii2b (f : Z -> Z -> bool) (a1 a2 : atom) : imonad val :=
  imonad_lift2 (fun i1 i2 => VBool (f i1 i2)) (interpret_atom a1 >>= unwrap_VInt) (interpret_atom a2 >>= unwrap_VInt).

Definition interpret_bb2b (f : bool -> bool -> bool) (a1 a2 : atom) : imonad val :=
  imonad_lift2 (fun b1 b2 => VBool (f b1 b2)) (interpret_atom a1 >>= unwrap_VBool) (interpret_atom a2 >>= unwrap_VBool).

Definition interpret_vv2b (f : val -> val -> bool) (a1 a2 : atom) : imonad val :=
  imonad_lift2 (fun v1 v2 => VBool (f v1 v2)) (interpret_atom a1) (interpret_atom a2).

Definition interpret_prim2 (p : prim2) : atom -> atom -> imonad val :=
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
  imonad_map (fun env => VFun (C1 env t)) imonad_ask_env.

Definition interpret_fix (t : term2) : imonad val :=
  imonad_map (fun env => VFix (C2 env t)) imonad_ask_env.

Definition interpret_pair (a1 a2 : atom) : imonad val :=
  imonad_lift2 VPair (interpret_atom a1) (interpret_atom a2).

Definition interpret_inl (a : atom) : imonad val :=
  VInl <$> interpret_atom a.

Definition interpret_inr (a : atom) : imonad val :=
  VInr <$> interpret_atom a.

Definition interpret_exn (tag : tag) (a : atom) : imonad val :=
  imonad_map (fun v => VExn (Exn tag v)) (interpret_atom a).

Definition interpret_ref (a : atom) : imonad val :=
  v <- interpret_atom a;
  h <- imonad_get_heap;
  match iheap_ref v h with
  | None => imonad_throw (MemoryError "")
  | Some (l, h') => VLoc l <$ imonad_set_heap h'
  end.

Definition interpret_get (a : atom) : imonad val :=
  l <- interpret_atom a >>= unwrap_VLoc;
  h <- imonad_get_heap;
  match iheap_get l h with
  | None => imonad_throw (MemoryError "")
  | Some v => imonad_pure v
  end.

Definition interpret_set (a1 a2 : atom) : imonad val :=
  l <- interpret_atom a1 >>= unwrap_VLoc;
  v <- interpret_atom a2;
  h <- imonad_get_heap;
  match iheap_set l v h with
  | None => imonad_throw (MemoryError "")
  | Some h' => VUnit <$ imonad_set_heap h'
  end.

Definition interpret_free (a : atom) : imonad val :=
  l <- interpret_atom a >>= unwrap_VLoc;
  h <- imonad_get_heap;
  match iheap_free l h with
  | None => imonad_throw (MemoryError "")
  | Some h' => VUnit <$ imonad_set_heap h'
  end.

Definition interpret_let : (env -> imonad iresult) -> imonad iresult :=
  imonad_bind imonad_ask_env.

Definition interpret_if (a : atom) (m1 m2 : imonad iresult) : imonad iresult :=
  b <- interpret_atom a >>= unwrap_VBool;
  if b then m1 else m2.

Definition interpret_split (a : atom) (f : val -> val -> imonad iresult) : imonad iresult :=
  v <- interpret_atom a;
  match v with
  | VPair v1 v2 => f v1 v2
  | _ => imonad_throw (TypeError "")
  end.

Definition interpret_case (a : atom) (f1 f2 : val -> imonad iresult) : imonad iresult :=
  v <- interpret_atom a;
  match v with
  | VInl v' => f1 v'
  | VInr v' => f2 v'
  | _ => imonad_throw (TypeError "")
  end.

Definition interpret_reset (k : kont) (m : imonad iresult) (f : val -> imonad iresult) : imonad iresult :=
  r <- m >>= handle_RShift;
  match r with
  | RReturn v => f v
  | RShift _ _ => imonad_throw (ControlError "unreachable")
  | RControl f' mk => imonad_pure (RControl f' (MKReset mk k))
  | RRaise _ => imonad_pure r
  end.

Definition interpret_prompt (k : kont) (m : imonad iresult) (f : val -> imonad iresult) : imonad iresult :=
  r <- m >>= handle_RControl;
  match r with
  | RReturn v => f v
  | RShift f' mk => imonad_pure (RShift f' (MKPrompt mk k))
  | RControl _ _ => imonad_throw (ControlError "unreachable")
  | RRaise _ => imonad_pure r
  end.

Definition interpret_try (k : kont) (t : exn_term) (m : imonad iresult) (f : val -> imonad iresult) (h : exn -> imonad iresult) : imonad iresult :=
  r <- m;
  match r with
  | RReturn v => f v
  | RShift f' mk => imonad_map (fun env => RShift f' (MKTry mk (ExnC env t) k)) imonad_ask_env
  | RControl f' mk => imonad_map (fun env => RControl f' (MKTry mk (ExnC env t) k)) imonad_ask_env
  | RRaise exn => h exn
  end.

Definition interpret_shift (k : kont) (f : env -> val -> imonad iresult) : imonad iresult :=
  imonad_map (fun env => RShift (f env >=> handle_RShift) (MKPure k)) imonad_ask_env.

Definition interpret_control (k : kont) (f : env -> val -> imonad iresult) : imonad iresult :=
  imonad_map (fun env => RControl (f env >=> handle_RControl) (MKPure k)) imonad_ask_env.

Definition interpret_raise (a : atom) : imonad iresult :=
  v <- interpret_atom a;
  match v with
  | VExn exn => imonad_pure (RRaise exn)
  | _ => imonad_throw (TypeError "")
  end.

Definition with_binder (b : binder) (v : val) (m : imonad iresult) : imonad iresult :=
  match b with
  | BAny => m
  | BVar x => imonad_local_env (EnvCons x v) m
  end.

Definition with_exn_pattern (p : pattern) (exn : exn) (m1 m2 : imonad iresult) : imonad iresult :=
  match p with
  | PAny => m1
  | PVar x => imonad_local_env (EnvCons x (VExn exn)) m1
  | PTag tag b => let (tag', v) := exn in if tag_eq_dec tag tag' then with_binder b v m1 else m2
  end.

Definition interpreter : Type := kont -> term -> imonad iresult.

Definition interpret_term1_with (rec : interpreter) (k : kont) (t : term1) (v : val) : imonad iresult :=
  let (b, t') := t in with_binder b v (rec k t').

Definition interpret_term2_with (rec : interpreter) (k : kont) (t : term2) (v1 v2 : val) : imonad iresult :=
  let (b1, b2, t') := t in with_binder b1 v1 (with_binder b2 v2 (rec k t')).

Fixpoint interpret_exn_term_with (rec : interpreter) (k : kont) (t : exn_term) (exn : exn) : imonad iresult :=
  match t with
  | ExnTBase p t' => with_exn_pattern p exn (rec k t') (imonad_pure (RRaise exn))
  | ExnTCons p t1 t2 => with_exn_pattern p exn (rec k t1) (interpret_exn_term_with rec k t2 exn)
  end.

Definition interpret_clo1_with (rec : interpreter) (k : kont) (c : clo1) (v : val) : imonad iresult :=
  let (env, t) := c in imonad_local_env (fun _ => env) (interpret_term1_with rec k t v).

Definition interpret_clo2_with (rec : interpreter) (k : kont) (c : clo2) (v1 v2 : val) : imonad iresult :=
  let (env, t) := c in imonad_local_env (fun _ => env) (interpret_term2_with rec k t v1 v2).

Definition interpret_exn_clo_with (rec : interpreter) (k : kont) (c : exn_clo) (exn : exn) : imonad iresult :=
  let (env, t) := c in imonad_local_env (fun _ => env) (interpret_exn_term_with rec k t exn).

Definition interpret_kont_with (rec : interpreter) (k : kont) (v : val) : imonad iresult :=
  match k with
  | KNil => imonad_pure (RReturn v)
  | KCons c k' => interpret_clo1_with rec k' c v
  end.

Definition interpret_K2Reset_with (rec : interpreter) (k : kont) (m : imonad iresult) : imonad iresult :=
  interpret_reset k m (interpret_kont_with rec k).

Definition interpret_K2Prompt_with (rec : interpreter) (k : kont) (m : imonad iresult) : imonad iresult :=
  interpret_prompt k m (interpret_kont_with rec k).

Definition interpret_K2Try_with (rec : interpreter) (k : kont) (m : imonad iresult) (c : exn_clo) : imonad iresult :=
  r <- m;
  match r with
  | RReturn v => interpret_kont_with rec k v
  | RShift f mk => imonad_pure (RShift f (MKTry mk c k))
  | RControl f mk => imonad_pure (RControl f (MKTry mk c k))
  | RRaise exn => interpret_exn_clo_with rec k c exn
  end.

Fixpoint interpret_metakont_with (rec : interpreter) (mk : metakont) (v : val) : imonad iresult :=
  match mk with
  | MKPure k => interpret_kont_with rec k v
  | MKReset mk' k => interpret_K2Reset_with rec k (interpret_metakont_with rec mk' v)
  | MKPrompt mk' k => interpret_K2Prompt_with rec k (interpret_metakont_with rec mk' v)
  | MKTry mk' c k => interpret_K2Try_with rec k (interpret_metakont_with rec mk' v) c
  end.

Definition interpret_app (rec : interpreter) (k : kont) (a1 a2 : atom) (f : val -> imonad iresult) : imonad iresult :=
  v <- interpret_atom a1;
  match v with
  | VFun c => interpret_atom a2 >>= interpret_clo1_with rec k c
  | VFix c => interpret_atom a2 >>= interpret_clo2_with rec k c v
  | VKontReset mk => interpret_reset k (interpret_atom a2 >>= interpret_metakont_with rec mk) f
  | VKont mk => interpret_atom a2 >>= interpret_metakont_with rec (metakont_extend mk k)
  | _ => imonad_throw (TypeError "")
  end.

Set Implicit Arguments.

Inductive term_graph : kont -> term -> Prop :=
| GTAtom k a : kont_graph k -> term_graph k (TAtom a)
| GTFun k t' : kont_graph k -> term_graph k (TFun t')
| GTFix k t' : kont_graph k -> term_graph k (TFix t')
| GTApp k a1 a2 : kont_graph k -> term_graph k (TApp a1 a2)
| GTLet k t1 t2 : (forall env, term_graph (KCons (C1 env t2) k) t1) -> term_graph k (TLet t1 t2)
| GTIf k a t1 t2 : term_graph k t1 -> term_graph k t2 -> term_graph k (TIf a t1 t2)
| GTPrim1 k p a : kont_graph k -> term_graph k (TPrim1 p a)
| GTPrim2 k p a1 a2 : kont_graph k -> term_graph k (TPrim2 p a1 a2)
| GTPair k a1 a2 : kont_graph k -> term_graph k (TPair a1 a2)
| GTSplit k a t' : term2_graph k t' -> term_graph k (TSplit a t')
| GTInl k a : kont_graph k -> term_graph k (TInl a)
| GTInr k a : kont_graph k -> term_graph k (TInr a)
| GTCase k a t1 t2 : term1_graph k t1 -> term1_graph k t2 -> term_graph k (TCase a t1 t2)
| GTRef k a : kont_graph k -> term_graph k (TRef a)
| GTGet k a : kont_graph k -> term_graph k (TGet a)
| GTSet k a1 a2 : kont_graph k -> term_graph k (TSet a1 a2)
| GTFree k a : kont_graph k -> term_graph k (TFree a)
| GTShift k t' : (forall env, clo1_graph KNil (C1 env t')) -> term_graph k (TShift t')
| GTReset k t' : term_graph KNil t' -> kont_graph k -> term_graph k (TReset t')
| GTControl k t' : (forall env, clo1_graph KNil (C1 env t')) -> term_graph k (TControl t')
| GTPrompt k t' : term_graph KNil t' -> kont_graph k -> term_graph k (TPrompt t')
| GTExn k tag a : kont_graph k -> term_graph k (TExn tag a)
| GTRaise k a : term_graph k (TRaise a)
| GTTry k t1 t2 : term_graph KNil t1 -> kont_graph k -> exn_term_graph k t2 -> term_graph k (TTry t1 t2)
with term1_graph : kont -> term1 -> Prop :=
| GT1 k b t' : term_graph k t' -> term1_graph k (T1 b t')
with term2_graph : kont -> term2 -> Prop :=
| GT2 k b1 b2 t' : term_graph k t' -> term2_graph k (T2 b1 b2 t')
with exn_term_graph : kont -> exn_term -> Prop :=
| GExnTBase k p t' : term_graph k t' -> exn_term_graph k (ExnTBase p t')
| GExnTCons k p t1 t2 : term_graph k t1 -> exn_term_graph k t2 -> exn_term_graph k (ExnTCons p t1 t2)
with clo1_graph : kont -> clo1 -> Prop :=
| GC1 k env t : term1_graph k t -> clo1_graph k (C1 env t)
with kont_graph : kont -> Prop :=
| GKNil : kont_graph KNil
| GKCons c k' : clo1_graph k' c -> kont_graph (KCons c k').

Lemma GTAtom_inv k a : term_graph k (TAtom a) -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTFun_inv k t' : term_graph k (TFun t') -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTFix_inv k t' : term_graph k (TFix t') -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTApp_inv k a1 a2 : term_graph k (TApp a1 a2) -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTLet_inv k t1 t2 : term_graph k (TLet t1 t2) -> forall env, term_graph (KCons (C1 env t2) k) t1.
Proof. inversion 1; auto. Defined.

Lemma GTIf_inv1 k a t1 t2 : term_graph k (TIf a t1 t2) -> term_graph k t1.
Proof. inversion 1; auto. Defined.

Lemma GTIf_inv2 k a t1 t2 : term_graph k (TIf a t1 t2) -> term_graph k t2.
Proof. inversion 1; auto. Defined.

Lemma GTPrim1_inv k p a : term_graph k (TPrim1 p a) -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTPrim2_inv k p a1 a2 : term_graph k (TPrim2 p a1 a2) -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTPair_inv k a1 a2 : term_graph k (TPair a1 a2) -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTSplit_inv k a t' : term_graph k (TSplit a t') -> term2_graph k t'.
Proof. inversion 1; auto. Defined.

Lemma GTInl_inv k a : term_graph k (TInl a) -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTInr_inv k a : term_graph k (TInr a) -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTCase_inv1 k a t1 t2 : term_graph k (TCase a t1 t2) -> term1_graph k t1.
Proof. inversion 1; auto. Defined.

Lemma GTCase_inv2 k a t1 t2 : term_graph k (TCase a t1 t2) -> term1_graph k t2.
Proof. inversion 1; auto. Defined.

Lemma GTRef_inv k a : term_graph k (TRef a) -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTGet_inv k a : term_graph k (TGet a) -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTSet_inv k a1 a2 : term_graph k (TSet a1 a2) -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTFree_inv k a : term_graph k (TFree a) -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTShift_inv k t' : term_graph k (TShift t') -> forall env, clo1_graph KNil (C1 env t').
Proof. inversion 1; auto. Defined.

Lemma GTReset_inv1 k t' : term_graph k (TReset t') -> term_graph KNil t'.
Proof. inversion 1; auto. Defined.

Lemma GTReset_inv2 k t' : term_graph k (TReset t') -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTControl_inv k t' : term_graph k (TControl t') -> forall env, clo1_graph KNil (C1 env t').
Proof. inversion 1; auto. Defined.

Lemma GTPrompt_inv1 k t' : term_graph k (TPrompt t') -> term_graph KNil t'.
Proof. inversion 1; auto. Defined.

Lemma GTPrompt_inv2 k t' : term_graph k (TPrompt t') -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTExn_inv k tag a : term_graph k (TExn tag a) -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTTry_inv1 k t1 t2 : term_graph k (TTry t1 t2) -> term_graph KNil t1.
Proof. inversion 1; auto. Defined.

Lemma GTTry_inv2 k t1 t2 : term_graph k (TTry t1 t2) -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTTry_inv3 k t1 t2 : term_graph k (TTry t1 t2) -> exn_term_graph k t2.
Proof. inversion 1; auto. Defined.

Lemma GT1_inv k b t' : term1_graph k (T1 b t') -> term_graph k t'.
Proof. inversion 1; auto. Defined.

Lemma GT2_inv k b1 b2 t' : term2_graph k (T2 b1 b2 t') -> term_graph k t'.
Proof. inversion 1; auto. Defined.

Lemma GExnTBase_inv k p t' : exn_term_graph k (ExnTBase p t') -> term_graph k t'.
Proof. inversion 1; auto. Defined.

Lemma GExnTCons_inv1 k p t1 t2 : exn_term_graph k (ExnTCons p t1 t2) -> term_graph k t1.
Proof. inversion 1; auto. Defined.

Lemma GExnTCons_inv2 k p t1 t2 : exn_term_graph k (ExnTCons p t1 t2) -> exn_term_graph k t2.
Proof. inversion 1; auto. Defined.

Lemma GC1_inv k env t : clo1_graph k (C1 env t) -> term1_graph k t.
Proof. inversion 1; auto. Defined.

Lemma GKCons_inv c k' : kont_graph (KCons c k') -> clo1_graph k' c.
Proof. inversion 1; auto. Defined.

Fixpoint build_term_graph_dep (k : kont) (G : kont_graph k) (t : term) : term_graph k t :=
  match t with
  | TAtom a => GTAtom a G
  | TFun t' => GTFun t' G
  | TFix t' => GTFix t' G
  | TApp a1 a2 => GTApp a1 a2 G
  | TLet t1 t2 => GTLet (fun env => build_term_graph_dep (GKCons (GC1 env (build_term1_graph_dep G t2))) t1)
  | TIf a t1 t2 => GTIf a (build_term_graph_dep G t1) (build_term_graph_dep G t2)
  | TPrim1 p a => GTPrim1 p a G
  | TPrim2 p a1 a2 => GTPrim2 p a1 a2 G
  | TPair a1 a2 => GTPair a1 a2 G
  | TSplit a t' => GTSplit a (build_term2_graph_dep G t')
  | TInl a => GTInl a G
  | TInr a => GTInr a G
  | TCase a t1 t2 => GTCase a (build_term1_graph_dep G t1) (build_term1_graph_dep G t2)
  | TRef a => GTRef a G
  | TGet a => GTGet a G
  | TSet a1 a2 => GTSet a1 a2 G
  | TFree a => GTFree a G
  | TShift t' => GTShift k (fun env => GC1 env (build_term1_graph_dep GKNil t'))
  | TReset t' => GTReset (build_term_graph_dep GKNil t') G
  | TControl t' => GTControl k (fun env => GC1 env (build_term1_graph_dep GKNil t'))
  | TPrompt t' => GTPrompt (build_term_graph_dep GKNil t') G
  | TExn tag a => GTExn tag a G
  | TRaise a => GTRaise k a
  | TTry t1 t2 => GTTry (build_term_graph_dep GKNil t1) G (build_exn_term_graph_dep G t2)
  end
with build_term1_graph_dep (k : kont) (G : kont_graph k) (t : term1) : term1_graph k t :=
  match t with
  | T1 b t' => GT1 b (build_term_graph_dep G t')
  end
with build_term2_graph_dep (k : kont) (G : kont_graph k) (t : term2) : term2_graph k t :=
  match t with
  | T2 b1 b2 t' => GT2 b1 b2 (build_term_graph_dep G t')
  end
with build_exn_term_graph_dep (k : kont) (G : kont_graph k) (t : exn_term) : exn_term_graph k t :=
  match t with
  | ExnTBase p t' => GExnTBase p (build_term_graph_dep G t')
  | ExnTCons p t1 t2 => GExnTCons p (build_term_graph_dep G t1) (build_exn_term_graph_dep G t2)
  end.

Definition build_clo1_graph_dep (k : kont) (G : kont_graph k) (c : clo1) : clo1_graph k c :=
  match c with
  | C1 env t => GC1 env (build_term1_graph_dep G t)
  end.

Fixpoint interpret_term_dep (rec : interpreter) (k : kont) (t : term) (G : term_graph k t) : imonad iresult :=
  match t return term_graph k t -> imonad iresult with
  | TAtom a => fun G => interpret_atom a >>= interpret_kont_dep rec (GTAtom_inv G)
  | TFun t' => fun G => interpret_fun t' >>= interpret_kont_dep rec (GTFun_inv G)
  | TFix t' => fun G => interpret_fix t' >>= interpret_kont_dep rec (GTFix_inv G)
  | TApp a1 a2 => fun G => interpret_app rec k a1 a2 (interpret_kont_dep rec (GTApp_inv G))
  | TLet t1 t2 => fun G => interpret_let (fun env => interpret_term_dep rec (GTLet_inv G env))
  | TIf a t1 t2 => fun G => interpret_if a (interpret_term_dep rec (GTIf_inv1 G)) (interpret_term_dep rec (GTIf_inv2 G))
  | TPrim1 p a => fun G => interpret_prim1 p a >>= interpret_kont_dep rec (GTPrim1_inv G)
  | TPrim2 p a1 a2 => fun G => interpret_prim2 p a1 a2 >>= interpret_kont_dep rec (GTPrim2_inv G)
  | TPair a1 a2 => fun G => interpret_pair a1 a2 >>= interpret_kont_dep rec (GTPair_inv G)
  | TSplit a t' => fun G => interpret_split a (interpret_term2_dep rec (GTSplit_inv G))
  | TInl a => fun G => interpret_inl a >>= interpret_kont_dep rec (GTInl_inv G)
  | TInr a => fun G => interpret_inr a >>= interpret_kont_dep rec (GTInr_inv G)
  | TCase a t1 t2 => fun G => interpret_case a (interpret_term1_dep rec (GTCase_inv1 G)) (interpret_term1_dep rec (GTCase_inv2 G))
  | TRef a => fun G => interpret_ref a >>= interpret_kont_dep rec (GTRef_inv G)
  | TGet a => fun G => interpret_get a >>= interpret_kont_dep rec (GTGet_inv G)
  | TSet a1 a2 => fun G => interpret_set a1 a2 >>= interpret_kont_dep rec (GTSet_inv G)
  | TFree a => fun G => interpret_free a >>= interpret_kont_dep rec (GTFree_inv G)
  | TShift t' => fun G => interpret_shift k (fun env => interpret_clo1_dep rec (GTShift_inv G env))
  | TReset t' => fun G => interpret_reset k (interpret_term_dep rec (GTReset_inv1 G)) (interpret_kont_dep rec (GTReset_inv2 G))
  | TControl t' => fun G => interpret_control k (fun env => interpret_clo1_dep rec (GTControl_inv G env))
  | TPrompt t' => fun G => interpret_prompt k (interpret_term_dep rec (GTPrompt_inv1 G)) (interpret_kont_dep rec (GTPrompt_inv2 G))
  | TExn tag a => fun G => interpret_exn tag a >>= interpret_kont_dep rec (GTExn_inv G)
  | TRaise a => fun G => interpret_raise a
  | TTry t1 t2 => fun G => interpret_try k t2
                             (interpret_term_dep rec (GTTry_inv1 G))
                             (interpret_kont_dep rec (GTTry_inv2 G))
                             (interpret_exn_term_dep rec (GTTry_inv3 G))
  end G
with interpret_term1_dep (rec : interpreter) (k : kont) (t : term1) (G : term1_graph k t) (v : val) : imonad iresult :=
  match t return term1_graph k t -> imonad iresult with
  | T1 b t' => fun G => with_binder b v (interpret_term_dep rec (GT1_inv G))
  end G
with interpret_term2_dep (rec : interpreter) (k : kont) (t : term2) (G : term2_graph k t) (v1 v2 : val) : imonad iresult :=
  match t return term2_graph k t -> imonad iresult with
  | T2 b1 b2 t' => fun G => with_binder b1 v1 (with_binder b2 v2 (interpret_term_dep rec (GT2_inv G)))
  end G
with interpret_exn_term_dep (rec : interpreter) (k : kont) (t : exn_term) (G : exn_term_graph k t) (exn : exn) : imonad iresult :=
  match t return exn_term_graph k t -> imonad iresult with
  | ExnTBase p t' => fun G => with_exn_pattern p exn (interpret_term_dep rec (GExnTBase_inv G)) (imonad_pure (RRaise exn))
  | ExnTCons p t1 t2 => fun G => with_exn_pattern p exn (interpret_term_dep rec (GExnTCons_inv1 G)) (interpret_exn_term_dep rec (GExnTCons_inv2 G) exn)
  end G
with interpret_clo1_dep (rec : interpreter) (k : kont) (c : clo1) (G : clo1_graph k c) (v : val) : imonad iresult :=
  match c return clo1_graph k c -> imonad iresult with
  | C1 env t => fun G => imonad_local_env (fun _ => env) (interpret_term1_dep rec (GC1_inv G) v)
  end G
with interpret_kont_dep (rec : interpreter) (k : kont) (G : kont_graph k) (v : val) : imonad iresult :=
  match k return kont_graph k -> imonad iresult with
  | KNil => fun G => imonad_pure (RReturn v)
  | KCons c k' => fun G => interpret_clo1_dep rec (GKCons_inv G) v
  end G.

Unset Implicit Arguments.

Fixpoint build_kont_graph (k : kont) : kont_graph k :=
  match k with
  | KNil => GKNil
  | KCons c k' => GKCons (build_clo1_graph_dep (build_kont_graph k') c)
  end.

Definition build_term_graph (k : kont) (t : term) : term_graph k t :=
  build_term_graph_dep (build_kont_graph k) t.

Definition interpret_term_aux (rec : interpreter) (k : kont) (t : term) : imonad iresult :=
  interpret_term_dep rec (build_term_graph k t).

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
