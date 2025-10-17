From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax env kont loc var.
From shift_reset.interpreter Require Import ierror iheap imonad.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope imonad_scope.
Local Unset Elimination Schemes.

Inductive iresult2S : Type :=
| R2SReturn : val -> iresult2S
| R2SBubble : (val -> imonad iresult2C) -> kont2C -> iresult2S
with iresult2C : Type :=
| R2CReturn : val -> iresult2C
| R2CBubble : (val -> imonad iresult2S) -> kont2S -> iresult2C.

Inductive iresult3 : Type :=
| R3Return : val -> iresult3
| R3BubbleS : (val -> imonad iresult2S) -> kont2S -> iresult3
| R3BubbleC : (val -> imonad iresult2C) -> kont2C -> iresult3.

Definition handle_R3BubbleS (r : iresult3) : imonad iresult2S :=
  match r with
  | R3Return v => imonad_pure (R2SReturn v)
  | R3BubbleS f ks => f (VKontS ks)
  | R3BubbleC f kc => imonad_pure (R2SBubble f kc)
  end.

Definition handle_R3BubbleC (r : iresult3) : imonad iresult2C :=
  match r with
  | R3Return v => imonad_pure (R2CReturn v)
  | R3BubbleS f ks => imonad_pure (R2CBubble f ks)
  | R3BubbleC f kc => f (VKontC kc)
  end.

Definition unwrap_R3Return (r : iresult3) : imonad val :=
  match r with
  | R3Return v => imonad_pure v
  | R3BubbleS _ _ => imonad_throw (ControlError "undelimited shift")
  | R3BubbleC _ _ => imonad_throw (ControlError "undelimited control")
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

Definition interpret_let : (env -> imonad iresult3) -> imonad iresult3 :=
  imonad_bind imonad_ask_env.

Definition interpret_if (a : atom) (m1 m2 : imonad iresult3) : imonad iresult3 :=
  b <- interpret_atom a >>= unwrap_VBool;
  if b then m1 else m2.

Definition interpret_split (a : atom) (f : val -> val -> imonad iresult3) : imonad iresult3 :=
  v <- interpret_atom a;
  match v with
  | VPair v1 v2 => f v1 v2
  | _ => imonad_throw (TypeError "")
  end.

Definition interpret_case (a : atom) (f1 f2 : val -> imonad iresult3) : imonad iresult3 :=
  v <- interpret_atom a;
  match v with
  | VInl v' => f1 v'
  | VInr v' => f2 v'
  | _ => imonad_throw (TypeError "")
  end.

Definition interpret_reset (k : kont1) (m : imonad iresult3) (f : val -> imonad iresult3) : imonad iresult3 :=
  r <- m >>= handle_R3BubbleS;
  match r with
  | R2SReturn v => f v
  | R2SBubble f' kc => imonad_pure (R3BubbleC f' (K2CSnoc kc k))
  end.

Definition interpret_prompt (k : kont1) (m : imonad iresult3) (f : val -> imonad iresult3) : imonad iresult3 :=
  r <- m >>= handle_R3BubbleC;
  match r with
  | R2CReturn v => f v
  | R2CBubble f' ks => imonad_pure (R3BubbleS f' (K2SSnoc ks k))
  end.

Definition interpret_shift (k : kont1) (f : env -> val -> imonad iresult3) : imonad iresult3 :=
  imonad_map (fun env => R3BubbleS (f env >=> handle_R3BubbleS) (K2SHead k)) imonad_ask_env.

Definition interpret_control (k : kont1) (f : env -> val -> imonad iresult3) : imonad iresult3 :=
  imonad_map (fun env => R3BubbleC (f env >=> handle_R3BubbleC) (K2CHead k)) imonad_ask_env.

Definition with_binder (b : binder) (v : val) (m : imonad iresult3) : imonad iresult3 :=
  match b with
  | BAnon => m
  | BVar x => imonad_local_env (ECons x v) m
  end.

Definition interpret_term1_with (rec : term -> imonad iresult3) (t : term1) (v : val) : imonad iresult3 :=
  let (b, t') := t in with_binder b v (rec t').

Definition interpret_term2_with (rec : term -> imonad iresult3) (t : term2) (v1 v2 : val) : imonad iresult3 :=
  let (b1, b2, t') := t in with_binder b1 v1 (with_binder b2 v2 (rec t')).

Definition interpret_clo1_with (rec : term -> imonad iresult3) (c : clo1) (v : val) : imonad iresult3 :=
  let (env, t) := c in imonad_local_env (fun _ => env) (interpret_term1_with rec t v).

Definition interpret_clo2_with (rec : term -> imonad iresult3) (c : clo2) (v1 v2 : val) : imonad iresult3 :=
  let (env, t) := c in imonad_local_env (fun _ => env) (interpret_term2_with rec t v1 v2).

Definition interpret_kont1_with (rec : kont1 -> term -> imonad iresult3) (k : kont1) (v : val) : imonad iresult3 :=
  match k with
  | K1Nil => imonad_pure (R3Return v)
  | K1Cons c k' => interpret_clo1_with (rec k') c v
  end.

Fixpoint interpret_kont2S_with (rec : kont1 -> term -> imonad iresult3) (ks : kont2S) (v : val) : imonad iresult3 :=
  match ks with
  | K2SHead k => interpret_kont1_with rec k v
  | K2SSnoc ks' k => interpret_prompt k (interpret_kont2S_with rec ks' v) (interpret_kont1_with rec k)
  end.

Fixpoint interpret_kont2C_with (rec : kont1 -> term -> imonad iresult3) (kc : kont2C) (v : val) : imonad iresult3 :=
  match kc with
  | K2CHead k => interpret_kont1_with rec k v
  | K2CSnoc kc' k => interpret_reset k (interpret_kont2C_with rec kc' v) (interpret_kont1_with rec k)
  end.

Definition interpret_app (rec : kont1 -> term -> imonad iresult3) (k : kont1) (a1 a2 : atom) (f : val -> imonad iresult3) : imonad iresult3 :=
  v <- interpret_atom a1;
  match v with
  | VFun c => interpret_atom a2 >>= interpret_clo1_with (rec k) c
  | VFix c => interpret_atom a2 >>= interpret_clo2_with (rec k) c v
  | VKontS ks => interpret_reset k (interpret_atom a2 >>= interpret_kont2S_with rec ks) f
  | VKontC kc => interpret_atom a2 >>= interpret_kont2C_with rec (kont2C_extend kc k)
  | _ => imonad_throw (TypeError "")
  end.

Set Implicit Arguments.

Inductive term_graph : kont1 -> term -> Prop :=
| GTAtom k a : kont1_graph k -> term_graph k (TAtom a)
| GTFun k t' : kont1_graph k -> term_graph k (TFun t')
| GTFix k t' : kont1_graph k -> term_graph k (TFix t')
| GTApp k a1 a2 : kont1_graph k -> term_graph k (TApp a1 a2)
| GTLet k t1 t2 : (forall env, term_graph (K1Cons (C1 env t2) k) t1) -> term_graph k (TLet t1 t2)
| GTIf k a t1 t2 : term_graph k t1 -> term_graph k t2 -> term_graph k (TIf a t1 t2)
| GTPrim1 k p a : kont1_graph k -> term_graph k (TPrim1 p a)
| GTPrim2 k p a1 a2 : kont1_graph k -> term_graph k (TPrim2 p a1 a2)
| GTPair k a1 a2 : kont1_graph k -> term_graph k (TPair a1 a2)
| GTSplit k a t' : term2_graph k t' -> term_graph k (TSplit a t')
| GTInl k a : kont1_graph k -> term_graph k (TInl a)
| GTInr k a : kont1_graph k -> term_graph k (TInr a)
| GTCase k a t1 t2 : term1_graph k t1 -> term1_graph k t2 -> term_graph k (TCase a t1 t2)
| GTRef k a : kont1_graph k -> term_graph k (TRef a)
| GTGet k a : kont1_graph k -> term_graph k (TGet a)
| GTSet k a1 a2 : kont1_graph k -> term_graph k (TSet a1 a2)
| GTFree k a : kont1_graph k -> term_graph k (TFree a)
| GTShift k t' : (forall env, clo1_graph K1Nil (C1 env t')) -> term_graph k (TShift t')
| GTReset k t' : term_graph K1Nil t' -> kont1_graph k -> term_graph k (TReset t')
| GTControl k t' : (forall env, clo1_graph K1Nil (C1 env t')) -> term_graph k (TControl t')
| GTPrompt k t' : term_graph K1Nil t' -> kont1_graph k -> term_graph k (TPrompt t')
with term1_graph : kont1 -> term1 -> Prop :=
| GT1 k b t' : term_graph k t' -> term1_graph k (T1 b t')
with term2_graph : kont1 -> term2 -> Prop :=
| GT2 k b1 b2 t' : term_graph k t' -> term2_graph k (T2 b1 b2 t')
with clo1_graph : kont1 -> clo1 -> Prop :=
| GC1 k env t : term1_graph k t -> clo1_graph k (C1 env t)
with kont1_graph : kont1 -> Prop :=
| GK1Nil : kont1_graph K1Nil
| GK1Cons c k' : clo1_graph k' c -> kont1_graph (K1Cons c k').

Lemma GTAtom_inv k a : term_graph k (TAtom a) -> kont1_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTFun_inv k t' : term_graph k (TFun t') -> kont1_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTFix_inv k t' : term_graph k (TFix t') -> kont1_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTApp_inv k a1 a2 : term_graph k (TApp a1 a2) -> kont1_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTLet_inv k t1 t2 : term_graph k (TLet t1 t2) -> forall env, term_graph (K1Cons (C1 env t2) k) t1.
Proof. inversion 1; auto. Defined.

Lemma GTIf_inv1 k a t1 t2 : term_graph k (TIf a t1 t2) -> term_graph k t1.
Proof. inversion 1; auto. Defined.

Lemma GTIf_inv2 k a t1 t2 : term_graph k (TIf a t1 t2) -> term_graph k t2.
Proof. inversion 1; auto. Defined.

Lemma GTPrim1_inv k p a : term_graph k (TPrim1 p a) -> kont1_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTPrim2_inv k p a1 a2 : term_graph k (TPrim2 p a1 a2) -> kont1_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTPair_inv k a1 a2 : term_graph k (TPair a1 a2) -> kont1_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTSplit_inv k a t' : term_graph k (TSplit a t') -> term2_graph k t'.
Proof. inversion 1; auto. Defined.

Lemma GTInl_inv k a : term_graph k (TInl a) -> kont1_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTInr_inv k a : term_graph k (TInr a) -> kont1_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTCase_inv1 k a t1 t2 : term_graph k (TCase a t1 t2) -> term1_graph k t1.
Proof. inversion 1; auto. Defined.

Lemma GTCase_inv2 k a t1 t2 : term_graph k (TCase a t1 t2) -> term1_graph k t2.
Proof. inversion 1; auto. Defined.

Lemma GTRef_inv k a : term_graph k (TRef a) -> kont1_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTGet_inv k a : term_graph k (TGet a) -> kont1_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTSet_inv k a1 a2 : term_graph k (TSet a1 a2) -> kont1_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTFree_inv k a : term_graph k (TFree a) -> kont1_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTShift_inv k t' : term_graph k (TShift t') -> forall env, clo1_graph K1Nil (C1 env t').
Proof. inversion 1; auto. Defined.

Lemma GTReset_inv1 k t' : term_graph k (TReset t') -> term_graph K1Nil t'.
Proof. inversion 1; auto. Defined.

Lemma GTReset_inv2 k t' : term_graph k (TReset t') -> kont1_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTControl_inv k t' : term_graph k (TControl t') -> forall env, clo1_graph K1Nil (C1 env t').
Proof. inversion 1; auto. Defined.

Lemma GTPrompt_inv1 k t' : term_graph k (TPrompt t') -> term_graph K1Nil t'.
Proof. inversion 1; auto. Defined.

Lemma GTPrompt_inv2 k t' : term_graph k (TPrompt t') -> kont1_graph k.
Proof. inversion 1; auto. Defined.

Lemma GT1_inv k b t' : term1_graph k (T1 b t') -> term_graph k t'.
Proof. inversion 1; auto. Defined.

Lemma GT2_inv k b1 b2 t' : term2_graph k (T2 b1 b2 t') -> term_graph k t'.
Proof. inversion 1; auto. Defined.

Lemma GC1_inv k env t : clo1_graph k (C1 env t) -> term1_graph k t.
Proof. inversion 1; auto. Defined.

Lemma GK1Cons_inv c k' : kont1_graph (K1Cons c k') -> clo1_graph k' c.
Proof. inversion 1; auto. Defined.

Fixpoint build_term_graph_dep (k : kont1) (G : kont1_graph k) (t : term) : term_graph k t :=
  match t with
  | TAtom a => GTAtom a G
  | TFun t' => GTFun t' G
  | TFix t' => GTFix t' G
  | TApp a1 a2 => GTApp a1 a2 G
  | TLet t1 t2 => GTLet (fun env => build_term_graph_dep (GK1Cons (GC1 env (build_term1_graph_dep G t2))) t1)
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
  | TShift t' => GTShift k (fun env => GC1 env (build_term1_graph_dep GK1Nil t'))
  | TReset t' => GTReset (build_term_graph_dep GK1Nil t') G
  | TControl t' => GTControl k (fun env => GC1 env (build_term1_graph_dep GK1Nil t'))
  | TPrompt t' => GTPrompt (build_term_graph_dep GK1Nil t') G
  end
with build_term1_graph_dep (k : kont1) (G : kont1_graph k) (t : term1) : term1_graph k t :=
  match t with
  | T1 b t' => GT1 b (build_term_graph_dep G t')
  end
with build_term2_graph_dep (k : kont1) (G : kont1_graph k) (t : term2) : term2_graph k t :=
  match t with
  | T2 b1 b2 t' => GT2 b1 b2 (build_term_graph_dep G t')
  end.

Definition build_clo1_graph_dep (k : kont1) (G : kont1_graph k) (c : clo1) : clo1_graph k c :=
  match c with
  | C1 env t => GC1 env (build_term1_graph_dep G t)
  end.

Fixpoint interpret_term_dep (rec : kont1 -> term -> imonad iresult3) (k : kont1) (t : term) (G : term_graph k t) : imonad iresult3 :=
  match t return term_graph k t -> imonad iresult3 with
  | TAtom a => fun G => interpret_atom a >>= interpret_kont1_dep rec (GTAtom_inv G)
  | TFun t' => fun G => interpret_fun t' >>= interpret_kont1_dep rec (GTFun_inv G)
  | TFix t' => fun G => interpret_fix t' >>= interpret_kont1_dep rec (GTFix_inv G)
  | TApp a1 a2 => fun G => interpret_app rec k a1 a2 (interpret_kont1_dep rec (GTApp_inv G))
  | TLet t1 t2 => fun G => interpret_let (fun env => interpret_term_dep rec (GTLet_inv G env))
  | TIf a t1 t2 => fun G => interpret_if a (interpret_term_dep rec (GTIf_inv1 G)) (interpret_term_dep rec (GTIf_inv2 G))
  | TPrim1 p a => fun G => interpret_prim1 p a >>= interpret_kont1_dep rec (GTPrim1_inv G)
  | TPrim2 p a1 a2 => fun G => interpret_prim2 p a1 a2 >>= interpret_kont1_dep rec (GTPrim2_inv G)
  | TPair a1 a2 => fun G => interpret_pair a1 a2 >>= interpret_kont1_dep rec (GTPair_inv G)
  | TSplit a t' => fun G => interpret_split a (interpret_term2_dep rec (GTSplit_inv G))
  | TInl a => fun G => interpret_inl a >>= interpret_kont1_dep rec (GTInl_inv G)
  | TInr a => fun G => interpret_inr a >>= interpret_kont1_dep rec (GTInr_inv G)
  | TCase a t1 t2 => fun G => interpret_case a (interpret_term1_dep rec (GTCase_inv1 G)) (interpret_term1_dep rec (GTCase_inv2 G))
  | TRef a => fun G => interpret_ref a >>= interpret_kont1_dep rec (GTRef_inv G)
  | TGet a => fun G => interpret_get a >>= interpret_kont1_dep rec (GTGet_inv G)
  | TSet a1 a2 => fun G => interpret_set a1 a2 >>= interpret_kont1_dep rec (GTSet_inv G)
  | TFree a => fun G => interpret_free a >>= interpret_kont1_dep rec (GTFree_inv G)
  | TShift t' => fun G => interpret_shift k (fun env => interpret_clo1_dep rec (GTShift_inv G env))
  | TReset t' => fun G => interpret_reset k (interpret_term_dep rec (GTReset_inv1 G)) (interpret_kont1_dep rec (GTReset_inv2 G))
  | TControl t' => fun G => interpret_control k (fun env => interpret_clo1_dep rec (GTControl_inv G env))
  | TPrompt t' => fun G => interpret_prompt k (interpret_term_dep rec (GTPrompt_inv1 G)) (interpret_kont1_dep rec (GTPrompt_inv2 G))
  end G
with interpret_term1_dep (rec : kont1 -> term -> imonad iresult3) (k : kont1) (t : term1) (G : term1_graph k t) (v : val) : imonad iresult3 :=
  match t return term1_graph k t -> imonad iresult3 with
  | T1 b t' => fun G => with_binder b v (interpret_term_dep rec (GT1_inv G))
  end G
with interpret_term2_dep (rec : kont1 -> term -> imonad iresult3) (k : kont1) (t : term2) (G : term2_graph k t) (v1 v2 : val) : imonad iresult3 :=
  match t return term2_graph k t -> imonad iresult3 with
  | T2 b1 b2 t' => fun G => with_binder b1 v1 (with_binder b2 v2 (interpret_term_dep rec (GT2_inv G)))
  end G
with interpret_clo1_dep (rec : kont1 -> term -> imonad iresult3) (k : kont1) (c : clo1) (G : clo1_graph k c) (v : val) : imonad iresult3 :=
  match c return clo1_graph k c -> imonad iresult3 with
  | C1 env t => fun G => imonad_local_env (fun _ => env) (interpret_term1_dep rec (GC1_inv G) v)
  end G
with interpret_kont1_dep (rec : kont1 -> term -> imonad iresult3) (k : kont1) (G : kont1_graph k) (v : val) : imonad iresult3 :=
  match k return kont1_graph k -> imonad iresult3 with
  | K1Nil => fun _ => imonad_pure (R3Return v)
  | K1Cons c k' => fun G => interpret_clo1_dep rec (GK1Cons_inv G) v
  end G.

Unset Implicit Arguments.

Fixpoint build_kont1_graph (k : kont1) : kont1_graph k :=
  match k with
  | K1Nil => GK1Nil
  | K1Cons c k' => GK1Cons (build_clo1_graph_dep (build_kont1_graph k') c)
  end.

Definition build_term_graph (k : kont1) (t : term) : term_graph k t :=
  build_term_graph_dep (build_kont1_graph k) t.

Definition interpret_term_aux (rec : kont1 -> term -> imonad iresult3) (k : kont1) (t : term) : imonad iresult3 :=
  interpret_term_dep rec (build_term_graph k t).

Fixpoint interpret_term (fuel : nat) (k : kont1) (t : term) : imonad iresult3 :=
  match fuel with
  | O => imonad_throw OutOfFuel
  | S fuel' => interpret_term_aux (interpret_term fuel') k t
  end.

Definition run_term (fuel : nat) (t : term) : (ierror + val) * iheap :=
  imonad_run (interpret_term fuel K1Nil t >>= unwrap_R3Return) ENil iheap_empty.

Definition eval_term (fuel : nat) (t : term) : ierror + val :=
  fst (run_term fuel t).

Definition exec_term (fuel : nat) (t : term) : iheap :=
  snd (run_term fuel t).
