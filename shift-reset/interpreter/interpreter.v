From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax env kont loc var.
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
  | P2Gt => interpret_ii2b Z.gtb m1 m2
  | P2Ge => interpret_ii2b Z.geb m1 m2
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

Definition interpret_term1_with (rec : term -> imonad val) (t : term1) (v : val) : imonad val :=
  let (b, t') := t in with_binder b v (rec t').

Definition interpret_term2_with (rec : term -> imonad val) (t : term2) (v1 v2 : val) : imonad val :=
  let (b1, b2, t') := t in with_binder b1 v1 (with_binder b2 v2 (rec t')).

Definition interpret_clo1_with (rec : term -> imonad val) (c : clo1) (m : imonad val) : imonad val :=
  imonad_bind m (fun v => let (env, t) := c in imonad_local_env (fun _ => env) (interpret_term1_with rec t v)).

Definition interpret_clo2_with (rec : term -> imonad val) (c : clo2) (f : val) (m : imonad val) : imonad val :=
  imonad_bind m (fun v => let (env, t) := c in imonad_local_env (fun _ => env) (interpret_term2_with rec t f v)).

Definition interpret_kont_with (rec : kont -> term -> imonad val) (k : kont) (m : imonad val) : imonad val :=
  match k with
  | KNil => m
  | KCons c k' => interpret_clo1_with (rec k') c m
  end.

Inductive delim : Type :=
| DNone : delim
| DReset : delim
| DPrompt : delim.

Set Implicit Arguments.

Inductive term_graph : delim -> kont -> term -> Prop :=
| GTAtom d k a : kont_graph d k -> term_graph d k (TAtom a)
| GTFun d k t' : kont_graph d k -> term_graph d k (TFun t')
| GTFix d k t' : kont_graph d k -> term_graph d k (TFix t')
| GTApp d k a1 a2 : kont_graph d k -> term_graph d k (TApp a1 a2)
| GTLet d k t1 t2 : (forall env, term_graph d (KCons (C1 env t2) k) t1) -> term_graph d k (TLet t1 t2)
| GTIf d k a t1 t2 : term_graph d k t1 -> term_graph d k t2 -> term_graph d k (TIf a t1 t2)
| GTPrim1 d k p a : kont_graph d k -> term_graph d k (TPrim1 p a)
| GTPrim2 d k p a1 a2 : kont_graph d k -> term_graph d k (TPrim2 p a1 a2)
| GTPair d k a1 a2 : kont_graph d k -> term_graph d k (TPair a1 a2)
| GTSplit d k a t' : term2_graph d k t' -> term_graph d k (TSplit a t')
| GTInl d k a : kont_graph d k -> term_graph d k (TInl a)
| GTInr d k a : kont_graph d k -> term_graph d k (TInr a)
| GTCase d k a t1 t2 : term1_graph d k t1 -> term1_graph d k t2 -> term_graph d k (TCase a t1 t2)
| GTRef d k a : kont_graph d k -> term_graph d k (TRef a)
| GTGet d k a : kont_graph d k -> term_graph d k (TGet a)
| GTSet d k a1 a2 : kont_graph d k -> term_graph d k (TSet a1 a2)
| GTFree d k a : kont_graph d k -> term_graph d k (TFree a)
| GTShiftX k t' : term_graph DNone k (TShift t')
| GTShiftS k t' : term1_graph DReset KNil t' -> term_graph DReset k (TShift t')
| GTShiftC k t' : term_graph DPrompt k (TShift t')
| GTReset d k t' : term_graph DReset KNil t' -> kont_graph d k -> term_graph d k (TReset t')
| GTControlX k t' : term_graph DNone k (TControl t')
| GTControlS k t' : term_graph DReset k (TControl t')
| GTControlC k t' : term1_graph DPrompt KNil t' -> term_graph DPrompt k (TControl t')
| GTPrompt d k t' : term_graph DPrompt KNil t' -> kont_graph d k -> term_graph d k (TPrompt t')
with term1_graph : delim -> kont -> term1 -> Prop :=
| GT1 d k b t' : term_graph d k t' -> term1_graph d k (T1 b t')
with term2_graph : delim -> kont -> term2 -> Prop :=
| GT2 d k b1 b2 t' : term_graph d k t' -> term2_graph d k (T2 b1 b2 t')
with clo1_graph : delim -> kont -> clo1 -> Prop :=
| GC1 d k env t : term1_graph d k t -> clo1_graph d k (C1 env t)
with kont_graph : delim -> kont -> Prop :=
| GKNil d : kont_graph d KNil
| GKCons d c k' : clo1_graph d k' c -> kont_graph d (KCons c k').

Lemma GTAtom_inv d k a : term_graph d k (TAtom a) -> kont_graph d k.
Proof. inversion 1; auto. Defined.

Lemma GTFun_inv d k t' : term_graph d k (TFun t') -> kont_graph d k.
Proof. inversion 1; auto. Defined.

Lemma GTFix_inv d k t' : term_graph d k (TFix t') -> kont_graph d k.
Proof. inversion 1; auto. Defined.

Lemma GTApp_inv d k a1 a2 : term_graph d k (TApp a1 a2) -> kont_graph d k.
Proof. inversion 1; auto. Defined.

Lemma GTLet_inv d k t1 t2 : term_graph d k (TLet t1 t2) -> forall env, term_graph d (KCons (C1 env t2) k) t1.
Proof. inversion 1; auto. Defined.

Lemma GTIf_inv1 d k a t1 t2 : term_graph d k (TIf a t1 t2) -> term_graph d k t1.
Proof. inversion 1; auto. Defined.

Lemma GTIf_inv2 d k a t1 t2 : term_graph d k (TIf a t1 t2) -> term_graph d k t2.
Proof. inversion 1; auto. Defined.

Lemma GTPrim1_inv d k p a : term_graph d k (TPrim1 p a) -> kont_graph d k.
Proof. inversion 1; auto. Defined.

Lemma GTPrim2_inv d k p a1 a2 : term_graph d k (TPrim2 p a1 a2) -> kont_graph d k.
Proof. inversion 1; auto. Defined.

Lemma GTPair_inv d k a1 a2 : term_graph d k (TPair a1 a2) -> kont_graph d k.
Proof. inversion 1; auto. Defined.

Lemma GTSplit_inv d k a t' : term_graph d k (TSplit a t') -> term2_graph d k t'.
Proof. inversion 1; auto. Defined.

Lemma GTInl_inv d k a : term_graph d k (TInl a) -> kont_graph d k.
Proof. inversion 1; auto. Defined.

Lemma GTInr_inv d k a : term_graph d k (TInr a) -> kont_graph d k.
Proof. inversion 1; auto. Defined.

Lemma GTCase_inv1 d k a t1 t2 : term_graph d k (TCase a t1 t2) -> term1_graph d k t1.
Proof. inversion 1; auto. Defined.

Lemma GTCase_inv2 d k a t1 t2 : term_graph d k (TCase a t1 t2) -> term1_graph d k t2.
Proof. inversion 1; auto. Defined.

Lemma GTRef_inv d k a : term_graph d k (TRef a) -> kont_graph d k.
Proof. inversion 1; auto. Defined.

Lemma GTGet_inv d k a : term_graph d k (TGet a) -> kont_graph d k.
Proof. inversion 1; auto. Defined.

Lemma GTSet_inv d k a1 a2 : term_graph d k (TSet a1 a2) -> kont_graph d k.
Proof. inversion 1; auto. Defined.

Lemma GTFree_inv d k a : term_graph d k (TFree a) -> kont_graph d k.
Proof. inversion 1; auto. Defined.

Lemma GTShiftS_inv k t' : term_graph DReset k (TShift t') -> term1_graph DReset KNil t'.
Proof. inversion 1; auto. Defined.

Lemma GTReset_inv1 d k t' : term_graph d k (TReset t') -> term_graph DReset KNil t'.
Proof. inversion 1; auto. Defined.

Lemma GTReset_inv2 d k t' : term_graph d k (TReset t') -> kont_graph d k.
Proof. inversion 1; auto. Defined.

Lemma GTControlC_inv k t' : term_graph DPrompt k (TControl t') -> term1_graph DPrompt KNil t'.
Proof. inversion 1; auto. Defined.

Lemma GTPrompt_inv1 d k t' : term_graph d k (TPrompt t') -> term_graph DPrompt KNil t'.
Proof. inversion 1; auto. Defined.

Lemma GTPrompt_inv2 d k t' : term_graph d k (TPrompt t') -> kont_graph d k.
Proof. inversion 1; auto. Defined.

Lemma GT1_inv d k b t' : term1_graph d k (T1 b t') -> term_graph d k t'.
Proof. inversion 1; auto. Defined.

Lemma GT2_inv d k b1 b2 t' : term2_graph d k (T2 b1 b2 t') -> term_graph d k t'.
Proof. inversion 1; auto. Defined.

Lemma GC1_inv d k env t : clo1_graph d k (C1 env t) -> term1_graph d k t.
Proof. inversion 1; auto. Defined.

Lemma GKCons_inv d c k' : kont_graph d (KCons c k') -> clo1_graph d k' c.
Proof. inversion 1; auto. Defined.

Fixpoint build_term_graph_dep d k (G : kont_graph d k) t : term_graph d k t :=
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
  | TShift t' =>
      match d with
      | DNone => GTShiftX k t'
      | DReset => GTShiftS k (build_term1_graph_dep (GKNil DReset) t')
      | DPrompt => GTShiftC k t'
      end
  | TReset t' => GTReset (build_term_graph_dep (GKNil DReset) t') G
  | TControl t' =>
      match d with
      | DNone => GTControlX k t'
      | DReset => GTControlS k t'
      | DPrompt => GTControlC k (build_term1_graph_dep (GKNil DPrompt) t')
      end
  | TPrompt t' => GTPrompt (build_term_graph_dep (GKNil DPrompt) t') G
  end
with build_term1_graph_dep d k (G : kont_graph d k) t : term1_graph d k t :=
  match t with
  | T1 b t' => GT1 b (build_term_graph_dep G t')
  end
with build_term2_graph_dep d k (G : kont_graph d k) t : term2_graph d k t :=
  match t with
  | T2 b1 b2 t' => GT2 b1 b2 (build_term_graph_dep G t')
  end.

Definition build_clo1_graph_dep d k (G : kont_graph d k) c : clo1_graph d k c :=
  match c with
  | C1 env t => GC1 env (build_term1_graph_dep G t)
  end.

Fixpoint interpret_term_dep (rec : delim -> kont -> term -> imonad val) d k t (G : term_graph d k t) : imonad val :=
  match t return term_graph d k t -> imonad val with
  | TAtom a => fun G => interpret_kont_dep rec (GTAtom_inv G) (interpret_atom a)
  | TFun t' => fun G => interpret_kont_dep rec (GTFun_inv G) (interpret_fun t')
  | TFix t' => fun G => interpret_kont_dep rec (GTFix_inv G) (interpret_fix t')
  | TApp a1 a2 =>
      fun G =>
        let m1 := interpret_atom a1 in
        let m2 := interpret_atom a2 in
        imonad_bind m1
          (fun v => match v with
                    | VFun c => interpret_clo1_with (rec d k) c m2
                    | VFix c => interpret_clo2_with (rec d k) c v m2
                    | VKontS k' => interpret_kont_dep rec (GTApp_inv G) (interpret_kont_with (rec DReset) k' m2)
                    | VKontC k' => interpret_kont_with (rec d) (kont_append k' k) m2
                    | _ => imonad_throw (TypeError "")
                    end)
  | TLet t1 t2 => fun G => imonad_bind imonad_ask_env (fun env => interpret_term_dep rec (GTLet_inv G env))
  | TIf a t1 t2 => fun G => interpret_if a (interpret_term_dep rec (GTIf_inv1 G)) (interpret_term_dep rec (GTIf_inv2 G))
  | TPrim1 p a => fun G => interpret_kont_dep rec (GTPrim1_inv G) (interpret_prim1 p a)
  | TPrim2 p a1 a2 => fun G => interpret_kont_dep rec (GTPrim2_inv G) (interpret_prim2 p a1 a2)
  | TPair a1 a2 => fun G => interpret_kont_dep rec (GTPair_inv G) (interpret_pair a1 a2)
  | TSplit a t' => fun G => interpret_split a (interpret_term2_dep rec (GTSplit_inv G))
  | TInl a => fun G => interpret_kont_dep rec (GTInl_inv G) (interpret_inl a)
  | TInr a => fun G => interpret_kont_dep rec (GTInr_inv G) (interpret_inr a)
  | TCase a t1 t2 => fun G => interpret_case a (interpret_term1_dep rec (GTCase_inv1 G)) (interpret_term1_dep rec (GTCase_inv2 G))
  | TRef a => fun G => interpret_kont_dep rec (GTRef_inv G) (interpret_ref a)
  | TGet a => fun G => interpret_kont_dep rec (GTGet_inv G) (interpret_get a)
  | TSet a1 a2 => fun G => interpret_kont_dep rec (GTSet_inv G) (interpret_set a1 a2)
  | TFree a => fun G => interpret_kont_dep rec (GTFree_inv G) (interpret_free a)
  | TShift t' =>
      match d return term_graph d k (TShift t') -> imonad val with
      | DNone => fun _ => imonad_throw (ControlError "")
      | DReset => fun G => interpret_term1_dep rec (GTShiftS_inv G) (VKontS k)
      | DPrompt => fun _ => imonad_throw (ControlError "")
      end
  | TReset t' => fun G => interpret_kont_dep rec (GTReset_inv2 G) (interpret_term_dep rec (GTReset_inv1 G))
  | TControl t' =>
      match d return term_graph d k (TControl t') -> imonad val with
      | DNone => fun _ => imonad_throw (ControlError "")
      | DReset => fun _ => imonad_throw (ControlError "")
      | DPrompt => fun G => interpret_term1_dep rec (GTControlC_inv G) (VKontC k)
      end
  | TPrompt t' => fun G => interpret_kont_dep rec (GTPrompt_inv2 G) (interpret_term_dep rec (GTPrompt_inv1 G))
  end G
with interpret_term1_dep (rec : delim -> kont -> term -> imonad val) d k t (G : term1_graph d k t) (v : val) : imonad val :=
  match t return term1_graph d k t -> imonad val with
  | T1 b t' => fun G => with_binder b v (interpret_term_dep rec (GT1_inv G))
  end G
with interpret_term2_dep (rec : delim -> kont -> term -> imonad val) d k t (G : term2_graph d k t) (v1 v2 : val) : imonad val :=
  match t return term2_graph d k t -> imonad val with
  | T2 b1 b2 t' => fun G => with_binder b1 v1 (with_binder b2 v2 (interpret_term_dep rec (GT2_inv G)))
  end G
with interpret_clo1_dep (rec : delim -> kont -> term -> imonad val) d k c (G : clo1_graph d k c) (m : imonad val) : imonad val :=
  imonad_bind m
    (fun v => match c return clo1_graph d k c -> imonad val with
              | C1 env t => fun G => imonad_local_env (fun _ => env) (interpret_term1_dep rec (GC1_inv G) v)
              end G)
with interpret_kont_dep (rec : delim -> kont -> term -> imonad val) d k (G : kont_graph d k) (m : imonad val) : imonad val :=
  match k return kont_graph d k -> imonad val with
  | KNil => fun _ => m
  | KCons c k' => fun G => interpret_clo1_dep rec (GKCons_inv G) m
  end G.

Unset Implicit Arguments.

Fixpoint build_kont_graph (d : delim) (k : kont) : kont_graph d k :=
  match k with
  | KNil => GKNil d
  | KCons c k' => GKCons (build_clo1_graph_dep (build_kont_graph d k') c)
  end.

Definition build_term_graph (d : delim) (k : kont) (t : term) : term_graph d k t :=
  build_term_graph_dep (build_kont_graph d k) t.

Definition interpret_term_aux (rec : delim -> kont -> term -> imonad val) (d : delim) (k : kont) (t : term) : imonad val :=
  interpret_term_dep rec (build_term_graph d k t).

Fixpoint interpret_term (fuel : nat) (d : delim) (k : kont) (t : term) : imonad val :=
  match fuel with
  | O => imonad_throw OutOfFuel
  | S fuel' => interpret_term_aux (interpret_term fuel') d k t
  end.

Definition run_term (fuel : nat) (t : term) : (ierror + val) * iheap :=
  imonad_run (interpret_term fuel DNone KNil t) ENil iheap_empty.

Definition eval_term (fuel : nat) (t : term) : ierror + val :=
  fst (run_term fuel t).

Definition exec_term (fuel : nat) (t : term) : iheap :=
  snd (run_term fuel t).
