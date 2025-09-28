From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax env loc var.
From shift_reset.interpreter Require Import ierror iheap imonad.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition interpret_atom (a : atom) : imonad val :=
  match a with
  | AUnit => imonad_pure VUnit
  | AInt i => imonad_pure (VInt i)
  | ABool b => imonad_pure (VBool b)
  | AVar x => imonad_bind imonad_ask_env
                (fun env => match env_lookup x env with
                            | None => imonad_throw (NameError (var_car x))
                            | Some v => imonad_pure v
                            end)
  end.

Definition interpret_fun (t : term1) : imonad val :=
  imonad_map (fun env => VFun (C1 env t)) imonad_ask_env.

Definition interpret_fix (t : term2) : imonad val :=
  imonad_map (fun env => VFix (C2 env t)) imonad_ask_env.

Definition unwrap_VInt_then (m : imonad val) (k : Z -> imonad val) : imonad val :=
  imonad_bind m
    (fun v => match v with
              | VInt i => k i
              | _ => imonad_throw (TypeError "")
              end).

Definition unwrap_VBool_then (m : imonad val) (k : bool -> imonad val) : imonad val :=
  imonad_bind m
    (fun v => match v with
              | VBool b => k b
              | _ => imonad_throw (TypeError "")
              end).

Definition unwrap_VLoc_then (m : imonad val) (k : loc -> imonad val) : imonad val :=
  imonad_bind m
    (fun v => match v with
              | VLoc l => k l
              | _ => imonad_throw (TypeError "")
              end).

Definition interpret_if (a : atom) (m1 m2 : imonad val) : imonad val :=
  unwrap_VBool_then (interpret_atom a) (fun b => if b then m1 else m2).

Definition interpret_i2i (f : Z -> Z) (m : imonad val) : imonad val :=
  unwrap_VInt_then m (fun i => imonad_pure (VInt (f i))).

Definition interpret_b2b (f : bool -> bool) (m : imonad val) : imonad val :=
  unwrap_VBool_then m (fun b => imonad_pure (VBool (f b))).

Definition interpret_prim1 (p : prim1) (a : atom) : imonad val :=
  let m := interpret_atom a in
  match p with
  | P1Neg => interpret_i2i Z.opp m
  | P1Not => interpret_b2b negb m
  end.

Definition interpret_ii2i (f : Z -> Z -> Z) (m1 m2 : imonad val) : imonad val :=
  unwrap_VInt_then m1 (fun i1 => unwrap_VInt_then m2 (fun i2 => imonad_pure (VInt (f i1 i2)))).

Definition interpret_ii2b (f : Z -> Z -> bool) (m1 m2 : imonad val) : imonad val :=
  unwrap_VInt_then m1 (fun i1 => unwrap_VInt_then m2 (fun i2 => imonad_pure (VBool (f i1 i2)))).

Definition interpret_bb2b (f : bool -> bool -> bool) (m1 m2 : imonad val) : imonad val :=
  unwrap_VBool_then m1 (fun b1 => unwrap_VBool_then m2 (fun b2 => imonad_pure (VBool (f b1 b2)))).

Definition interpret_prim2 (p : prim2) (a1 a2 : atom) : imonad val :=
  let m1 := interpret_atom a1 in
  let m2 := interpret_atom a2 in
  match p with
  | P2Add => interpret_ii2i Z.add m1 m2
  | P2Sub => interpret_ii2i Z.sub m1 m2
  | P2Mul => interpret_ii2i Z.mul m1 m2
  | P2Div => interpret_ii2i Z.div m1 m2
  | P2Rem => interpret_ii2i Z.rem m1 m2
  | P2Lt => interpret_ii2b Z.ltb m1 m2
  | P2Le => interpret_ii2b Z.leb m1 m2
  | P2And => interpret_bb2b andb m1 m2
  | P2Or => interpret_bb2b orb m1 m2
  | P2Xor => interpret_bb2b xorb m1 m2
  | P2Eq => imonad_lift2 (fun v1 v2 => VBool (val_eqb v1 v2)) m1 m2
  | P2Neq => imonad_lift2 (fun v1 v2 => VBool (val_neqb v1 v2)) m1 m2
  end.

Definition interpret_pair (a1 a2 : atom) : imonad val :=
  imonad_lift2 VPair (interpret_atom a1) (interpret_atom a2).

Definition interpret_split (a : atom) (k : val -> val -> imonad val) : imonad val :=
  imonad_bind (interpret_atom a)
    (fun v => match v with
              | VPair v1 v2 => k v1 v2
              | _ => imonad_throw (TypeError "")
              end).

Definition interpret_inl (a : atom) : imonad val :=
  imonad_map VInl (interpret_atom a).

Definition interpret_inr (a : atom) : imonad val :=
  imonad_map VInr (interpret_atom a).

Definition interpret_case (a : atom) (k1 k2 : val -> imonad val) : imonad val :=
  imonad_bind (interpret_atom a)
    (fun v => match v with
              | VInl v' => k1 v'
              | VInr v' => k2 v'
              | _ => imonad_throw (TypeError "")
              end).

Definition interpret_ref (a : atom) : imonad val :=
  imonad_bind (interpret_atom a)
    (fun v => imonad_bind imonad_get_heap
                (fun h => match iheap_ref v h with
                          | None => imonad_throw (MemoryError "")
                          | Some (l, h') => imonad_then (imonad_set_heap h') (imonad_pure (VLoc l))
                          end)).

Definition interpret_get (a : atom) : imonad val :=
  unwrap_VLoc_then (interpret_atom a)
    (fun l => imonad_bind imonad_get_heap
                (fun h => match iheap_get l h with
                          | None => imonad_throw (MemoryError "")
                          | Some v => imonad_pure v
                          end)).

Definition interpret_set (a1 a2 : atom) : imonad val :=
  let m1 := interpret_atom a1 in
  let m2 := interpret_atom a2 in
  unwrap_VLoc_then m1
    (fun l => imonad_bind m2
                (fun v => imonad_bind imonad_get_heap
                            (fun h => match iheap_set l v h with
                                      | None => imonad_throw (MemoryError "")
                                      | Some h' => imonad_then (imonad_set_heap h') (imonad_pure VUnit)
                                      end))).

Definition interpret_free (a : atom) : imonad val :=
  unwrap_VLoc_then (interpret_atom a)
    (fun l => imonad_bind imonad_get_heap
                (fun h => match iheap_free l h with
                          | None => imonad_throw (MemoryError "")
                          | Some h' => imonad_then (imonad_set_heap h') (imonad_pure VUnit)
                          end)).

Definition with_binder (b : binder) (v : val) (m : imonad val) : imonad val :=
  match b with
  | BAnon => m
  | BVar x => imonad_local_env (ECons x v) m
  end.

Definition with_env (env : env) : imonad val -> imonad val :=
  imonad_local_env (fun _ => env).

Definition interpret_term1_with (rec : term -> imonad val) (t : term1) (m : imonad val) : imonad val :=
  imonad_bind m (fun v => let (b, t') := t in with_binder b v (rec t')).

Definition interpret_term2_with (rec : term -> imonad val) (t : term2) (v : val) (m : imonad val) : imonad val :=
  imonad_bind m (fun v' => let (b1, b2, t') := t in with_binder b1 v (with_binder b2 v' (rec t'))).

Definition interpret_clo1_with (rec : term -> imonad val) (c : clo1) (m : imonad val) : imonad val :=
  let (env, t) := c in with_env env (interpret_term1_with rec t m).

Definition interpret_clo2_with (rec : term -> imonad val) (c : clo2) (v : val) (m : imonad val) : imonad val :=
  let (env, t) := c in with_env env (interpret_term2_with rec t v m).

Definition interpret_kont_with (rec : term -> kont -> imonad val) (k : kont) (m : imonad val) : imonad val :=
  match k with
  | KNil => m
  | KCons c k' => interpret_clo1_with (fun t => rec t k') c m
  end.

Set Implicit Arguments.

Inductive term_kont_graph : term -> kont -> Prop :=
| GTAtom a k : kont_graph k -> term_kont_graph (TAtom a) k
| GTFun t k : kont_graph k -> term_kont_graph (TFun t) k
| GTFix t k : kont_graph k -> term_kont_graph (TFix t) k
| GTApp a1 a2 k : kont_graph k -> term_kont_graph (TApp a1 a2) k
| GTLet t1 t2 k : (forall env, term_kont_graph t1 (KCons (C1 env t2) k)) -> term_kont_graph (TLet t1 t2) k
| GTIf a t1 t2 k : term_kont_graph t1 k -> term_kont_graph t2 k -> term_kont_graph (TIf a t1 t2) k
| GTPrim1 p a k : kont_graph k -> term_kont_graph (TPrim1 p a) k
| GTPrim2 p a1 a2 k : kont_graph k -> term_kont_graph (TPrim2 p a1 a2) k
| GTPair a1 a2 k : kont_graph k -> term_kont_graph (TPair a1 a2) k
| GTSplit a t k : term2_kont_graph t k -> term_kont_graph (TSplit a t) k
| GTInl a k : kont_graph k -> term_kont_graph (TInl a) k
| GTInr a k : kont_graph k -> term_kont_graph (TInr a) k
| GTCase a t1 t2 k : term1_kont_graph t1 k -> term1_kont_graph t2 k -> term_kont_graph (TCase a t1 t2) k
| GTRef a k : kont_graph k -> term_kont_graph (TRef a) k
| GTGet a k : kont_graph k -> term_kont_graph (TGet a) k
| GTSet a1 a2 k : kont_graph k -> term_kont_graph (TSet a1 a2) k
| GTFree a k : kont_graph k -> term_kont_graph (TFree a) k
| GTShift t k : term1_kont_graph t KNil -> term_kont_graph (TShift t) k
| GTReset t k : term_kont_graph t KNil -> kont_graph k -> term_kont_graph (TReset t) k
with term1_kont_graph : term1 -> kont -> Prop :=
| GT1 b t k : term_kont_graph t k -> term1_kont_graph (T1 b t) k
with term2_kont_graph : term2 -> kont -> Prop :=
| GT2 b1 b2 t k : term_kont_graph t k -> term2_kont_graph (T2 b1 b2 t) k
with clo1_kont_graph : clo1 -> kont -> Prop :=
| GC1 env t k : term1_kont_graph t k -> clo1_kont_graph (C1 env t) k
with kont_graph : kont -> Prop :=
| GKNil : kont_graph KNil
| GKCons c k : clo1_kont_graph c k -> kont_graph (KCons c k).

Lemma GTAtom_inv : forall a k, term_kont_graph (TAtom a) k -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTFun_inv : forall t k, term_kont_graph (TFun t) k -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTFix_inv : forall t k, term_kont_graph (TFix t) k -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTApp_inv : forall a1 a2 k, term_kont_graph (TApp a1 a2) k -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTLet_inv : forall t1 t2 k, term_kont_graph (TLet t1 t2) k -> forall env, term_kont_graph t1 (KCons (C1 env t2) k).
Proof. inversion 1; auto. Defined.

Lemma GTIf_inv1 : forall a t1 t2 k, term_kont_graph (TIf a t1 t2) k -> term_kont_graph t1 k.
Proof. inversion 1; auto. Defined.

Lemma GTIf_inv2 : forall a t1 t2 k, term_kont_graph (TIf a t1 t2) k -> term_kont_graph t2 k.
Proof. inversion 1; auto. Defined.

Lemma GTPrim1_inv : forall p a k, term_kont_graph (TPrim1 p a) k -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTPrim2_inv : forall p a1 a2 k, term_kont_graph (TPrim2 p a1 a2) k -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTPair_inv : forall a1 a2 k, term_kont_graph (TPair a1 a2) k -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTSplit_inv : forall a t k, term_kont_graph (TSplit a t) k -> term2_kont_graph t k.
Proof. inversion 1; auto. Defined.

Lemma GTInl_inv : forall a k, term_kont_graph (TInl a) k -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTInr_inv : forall a k, term_kont_graph (TInr a) k -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTCase_inv1 : forall a t1 t2 k, term_kont_graph (TCase a t1 t2) k -> term1_kont_graph t1 k.
Proof. inversion 1; auto. Defined.

Lemma GTCase_inv2 : forall a t1 t2 k, term_kont_graph (TCase a t1 t2) k -> term1_kont_graph t2 k.
Proof. inversion 1; auto. Defined.

Lemma GTRef_inv : forall a k, term_kont_graph (TRef a) k -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTGet_inv : forall a k, term_kont_graph (TGet a) k -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTSet_inv : forall a1 a2 k, term_kont_graph (TSet a1 a2) k -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTFree_inv : forall a k, term_kont_graph (TFree a) k -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTShift_inv : forall t k, term_kont_graph (TShift t) k -> term1_kont_graph t KNil.
Proof. inversion 1; auto. Defined.

Lemma GTReset_inv1 : forall t k, term_kont_graph (TReset t) k -> term_kont_graph t KNil.
Proof. inversion 1; auto. Defined.

Lemma GTReset_inv2 : forall t k, term_kont_graph (TReset t) k -> kont_graph k.
Proof. inversion 1; auto. Defined.

Lemma GT1_inv : forall b t k, term1_kont_graph (T1 b t) k -> term_kont_graph t k.
Proof. inversion 1; auto. Defined.

Lemma GT2_inv : forall b1 b2 t k, term2_kont_graph (T2 b1 b2 t) k -> term_kont_graph t k.
Proof. inversion 1; auto. Defined.

Lemma GC1_inv : forall env t k, clo1_kont_graph (C1 env t) k -> term1_kont_graph t k.
Proof. inversion 1; auto. Defined.

Lemma GKCons_inv : forall c k, kont_graph (KCons c k) -> clo1_kont_graph c k.
Proof. inversion 1; auto. Defined.

Fixpoint compute_term_kont_graph_dep (t : term) (k : kont) (G : kont_graph k) : term_kont_graph t k :=
  match t with
  | TAtom a => GTAtom a G
  | TFun t' => GTFun t' G
  | TFix t' => GTFix t' G
  | TApp a1 a2 => GTApp a1 a2 G
  | TLet t1 t2 => GTLet (fun env => compute_term_kont_graph_dep t1 (GKCons (GC1 env (compute_term1_kont_graph_dep t2 G))))
  | TIf a t1 t2 => GTIf a (compute_term_kont_graph_dep t1 G) (compute_term_kont_graph_dep t2 G)
  | TPrim1 p a => GTPrim1 p a G
  | TPrim2 p a1 a2 => GTPrim2 p a1 a2 G
  | TPair a1 a2 => GTPair a1 a2 G
  | TSplit a t' => GTSplit a (compute_term2_kont_graph_dep t' G)
  | TInl a => GTInl a G
  | TInr a => GTInr a G
  | TCase a t1 t2 => GTCase a (compute_term1_kont_graph_dep t1 G) (compute_term1_kont_graph_dep t2 G)
  | TRef a => GTRef a G
  | TGet a => GTGet a G
  | TSet a1 a2 => GTSet a1 a2 G
  | TFree a => GTFree a G
  | TShift t' => GTShift k (compute_term1_kont_graph_dep t' GKNil)
  | TReset t' => GTReset (compute_term_kont_graph_dep t' GKNil) G
  end
with compute_term1_kont_graph_dep (t : term1) (k : kont) (G : kont_graph k) : term1_kont_graph t k :=
  match t with
  | T1 b t' => GT1 b (compute_term_kont_graph_dep t' G)
  end
with compute_term2_kont_graph_dep (t : term2) (k : kont) (G : kont_graph k) : term2_kont_graph t k :=
  match t with
  | T2 b1 b2 t' => GT2 b1 b2 (compute_term_kont_graph_dep t' G)
  end.

Definition compute_clo1_kont_graph_dep (c : clo1) (k : kont) (G : kont_graph k) : clo1_kont_graph c k :=
  match c with
  | C1 env t => GC1 env (compute_term1_kont_graph_dep t G)
  end.

Record irec_kont : Type := IRecKont { app_irec_kont : term -> kont -> imonad val }.

Fixpoint interpret_term_kont_dep (rec : irec_kont) (t : term) (k : kont) (G : term_kont_graph t k) : imonad val :=
  match t return term_kont_graph t k -> imonad val with
  | TAtom a => fun G => interpret_kont_dep rec (GTAtom_inv G) (interpret_atom a)
  | TFun t' => fun G => interpret_kont_dep rec (GTFun_inv G) (interpret_fun t')
  | TFix t' => fun G => interpret_kont_dep rec (GTFix_inv G) (interpret_fix t')
  | TApp a1 a2 => fun G =>
                    let m1 := interpret_atom a1 in
                    let m2 := interpret_atom a2 in
                    imonad_bind m1
                      (fun v => match v with
                                | VFun c => interpret_clo1_with (fun t' => app_irec_kont rec t k) c m2
                                | VFix c => interpret_clo2_with (fun t' => app_irec_kont rec t k) c v m2
                                | VKont k' => interpret_kont_dep rec (GTApp_inv G) (interpret_kont_with (app_irec_kont rec) k m2)
                                | _ => imonad_throw (TypeError "")
                                end)
  | TLet t1 t2 => fun G => imonad_bind imonad_ask_env (fun env => interpret_term_kont_dep rec (GTLet_inv G env))
  | TIf a t1 t2 => fun G => interpret_if a (interpret_term_kont_dep rec (GTIf_inv1 G)) (interpret_term_kont_dep rec (GTIf_inv2 G))
  | TPrim1 p a => fun G => interpret_kont_dep rec (GTPrim1_inv G) (interpret_prim1 p a)
  | TPrim2 p a1 a2 => fun G => interpret_kont_dep rec (GTPrim2_inv G) (interpret_prim2 p a1 a2)
  | TPair a1 a2 => fun G => interpret_kont_dep rec (GTPair_inv G) (interpret_pair a1 a2)
  | TSplit a t' => fun G => interpret_split a (interpret_term2_kont_dep rec (GTSplit_inv G))
  | TInl a => fun G => interpret_kont_dep rec (GTInl_inv G) (interpret_inl a)
  | TInr a => fun G => interpret_kont_dep rec (GTInr_inv G) (interpret_inr a)
  | TCase a t1 t2 => fun G => interpret_case a (interpret_term1_kont_dep rec (GTCase_inv1 G)) (interpret_term1_kont_dep rec (GTCase_inv2 G))
  | TRef a => fun G => interpret_kont_dep rec (GTRef_inv G) (interpret_ref a)
  | TGet a => fun G => interpret_kont_dep rec (GTGet_inv G) (interpret_get a)
  | TSet a1 a2 => fun G => interpret_kont_dep rec (GTSet_inv G) (interpret_set a1 a2)
  | TFree a => fun G => interpret_kont_dep rec (GTFree_inv G) (interpret_free a)
  | TShift t' => fun G => interpret_term1_kont_dep rec (GTShift_inv G) (VKont k)
  | TReset t' => fun G => interpret_kont_dep rec (GTReset_inv2 G) (interpret_term_kont_dep rec (GTReset_inv1 G))
  end G
with interpret_term1_kont_dep (rec : irec_kont) (t : term1) (k : kont) (G : term1_kont_graph t k) (v : val) : imonad val :=
  match t return term1_kont_graph t k -> imonad val with
  | T1 b t' => fun G => with_binder b v (interpret_term_kont_dep rec (GT1_inv G))
  end G
with interpret_term2_kont_dep (rec : irec_kont) (t : term2) (k : kont) (G : term2_kont_graph t k) (v1 v2 : val) : imonad val :=
  match t return term2_kont_graph t k -> imonad val with
  | T2 b1 b2 t' => fun G => with_binder b1 v1 (with_binder b2 v2 (interpret_term_kont_dep rec (GT2_inv G)))
  end G
with interpret_clo1_kont_dep (rec : irec_kont) (c : clo1) (k : kont) (G : clo1_kont_graph c k) (v : val) : imonad val :=
  match c return clo1_kont_graph c k -> imonad val with
  | C1 env t => fun G => with_env env (interpret_term1_kont_dep rec (GC1_inv G) v)
  end G
with interpret_kont_dep (rec : irec_kont) (k : kont) (G : kont_graph k) (m : imonad val) : imonad val :=
  match k return kont_graph k -> imonad val with
  | KNil => fun _ => m
  | KCons c k' => fun G => imonad_bind m (interpret_clo1_kont_dep rec (GKCons_inv G))
  end G.

Unset Implicit Arguments.

Fixpoint compute_kont_graph (k : kont) : kont_graph k :=
  match k with
  | KNil => GKNil
  | KCons c k' => GKCons (compute_clo1_kont_graph_dep c (compute_kont_graph k'))
  end.

Definition compute_term_kont_graph (t : term) (k : kont) : term_kont_graph t k :=
  compute_term_kont_graph_dep t (compute_kont_graph k).

Definition interpret_term_kont_aux (rec : irec_kont) (t : term) (k : kont) : imonad val :=
  interpret_term_kont_dep rec (compute_term_kont_graph t k).

Fixpoint interpret_term_kont (fuel : nat) (t : term) (k : kont) : imonad val :=
  match fuel with
  | O => imonad_throw OutOfFuel
  | S fuel' => interpret_term_kont_aux (IRecKont (interpret_term_kont fuel')) t k
  end.

Record irec : Type := IRec { app_irec : term -> imonad val; app_kont_irec : term -> kont -> imonad val }.

Fixpoint interpret_term_aux (rec : irec) (t : term) : imonad val :=
  match t with
  | TAtom a => interpret_atom a
  | TFun t' => interpret_fun t'
  | TFix t' => interpret_fix t'
  | TApp a1 a2 => let m1 := interpret_atom a1 in
                  let m2 := interpret_atom a2 in
                  imonad_bind m1
                    (fun v => match v with
                              | VFun c => interpret_clo1_with (app_irec rec) c m2
                              | VFix c => interpret_clo2_with (app_irec rec) c v m2
                              | VKont k => interpret_kont_with (app_kont_irec rec) k m2
                              | _ => imonad_throw (TypeError "not a fun/fix/kont")
                              end)
  | TLet t1 t2 => imonad_bind (interpret_term_aux rec t1) (interpret_term1_aux rec t2)
  | TIf a t1 t2 => interpret_if a (interpret_term_aux rec t1) (interpret_term_aux rec t2)
  | TPrim1 p a => interpret_prim1 p a
  | TPrim2 p a1 a2 => interpret_prim2 p a1 a2
  | TPair a1 a2 => interpret_pair a1 a2
  | TSplit a t' => interpret_split a (interpret_term2_aux rec t')
  | TInl a => interpret_inl a
  | TInr a => interpret_inr a
  | TCase a t1 t2 => interpret_case a (interpret_term1_aux rec t1) (interpret_term1_aux rec t2)
  | TRef a => interpret_ref a
  | TGet a => interpret_get a
  | TSet a1 a2 => interpret_set a1 a2
  | TFree a => interpret_free a
  | TShift _ => imonad_throw (ControlError "shift without enclosing reset")
  | TReset t' => interpret_term_kont_aux (IRecKont (app_kont_irec rec)) t' KNil
  end
with interpret_term1_aux (rec : irec) (t : term1) (v : val) : imonad val :=
  let (b, t') := t in with_binder b v (interpret_term_aux rec t')
with interpret_term2_aux (rec : irec) (t : term2) (v1 v2 : val) : imonad val :=
  let (b1, b2, t') := t in with_binder b1 v1 (with_binder b2 v2 (interpret_term_aux rec t')).

Fixpoint interpret_term (fuel : nat) (t : term) : imonad val :=
  match fuel with
  | O => imonad_throw OutOfFuel
  | S fuel' => interpret_term_aux (IRec (interpret_term fuel') (interpret_term_kont fuel')) t
  end.

Definition run_term (fuel : nat) (t : term) : (ierror + val) * iheap :=
  imonad_run (interpret_term fuel t) ENil iheap_empty.

Definition eval_term (fuel : nat) (t : term) : ierror + val :=
  fst (run_term fuel t).

Definition exec_term (fuel : nat) (t : term) : iheap :=
  snd (run_term fuel t).
