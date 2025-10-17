From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax env kont loc var.
From shift_reset.interpreter Require Import ierror iheap imonad.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Inductive iresult : Type :=
| RReturn : val -> iresult
| RBubbleS : (val -> imonad iresult) -> kont2S -> iresult
| RBubbleC : (val -> imonad iresult) -> kont2C -> iresult.

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

Definition unwrap_VInt_then {A} (m : imonad val) (k : Z -> imonad A) : imonad A :=
  imonad_bind m
    (fun v => match v with
              | VInt i => k i
              | _ => imonad_throw (TypeError "")
              end).

Definition unwrap_VBool_then {A} (m : imonad val) (k : bool -> imonad A) : imonad A :=
  imonad_bind m
    (fun v => match v with
              | VBool b => k b
              | _ => imonad_throw (TypeError "")
              end).

Definition unwrap_VLoc_then {A} (m : imonad val) (k : loc -> imonad A) : imonad A :=
  imonad_bind m
    (fun v => match v with
              | VLoc l => k l
              | _ => imonad_throw (TypeError "")
              end).

Definition interpret_if (a : atom) (m1 m2 : imonad iresult) : imonad iresult :=
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

Definition interpret_split (a : atom) (k : val -> val -> imonad iresult) : imonad iresult :=
  imonad_bind (interpret_atom a)
    (fun v => match v with
              | VPair v1 v2 => k v1 v2
              | _ => imonad_throw (TypeError "")
              end).

Definition interpret_inl (a : atom) : imonad val :=
  imonad_map VInl (interpret_atom a).

Definition interpret_inr (a : atom) : imonad val :=
  imonad_map VInr (interpret_atom a).

Definition interpret_case (a : atom) (k1 k2 : val -> imonad iresult) : imonad iresult :=
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

Definition with_binder (b : binder) (v : val) (m : imonad iresult) : imonad iresult :=
  match b with
  | BAnon => m
  | BVar x => imonad_local_env (ECons x v) m
  end.

Definition interpret_term1_with (rec : term -> imonad iresult) (t : term1) (v : val) : imonad iresult :=
  let (b, t') := t in with_binder b v (rec t').

Definition interpret_term2_with (rec : term -> imonad iresult) (t : term2) (v1 v2 : val) : imonad iresult :=
  let (b1, b2, t') := t in with_binder b1 v1 (with_binder b2 v2 (rec t')).

Definition interpret_clo1_with (rec : term -> imonad iresult) (c : clo1) (m : imonad val) : imonad iresult :=
  imonad_bind m (fun v => let (env, t) := c in imonad_local_env (fun _ => env) (interpret_term1_with rec t v)).

Definition interpret_clo2_with (rec : term -> imonad iresult) (c : clo2) (f : val) (m : imonad val) : imonad iresult :=
  imonad_bind m (fun v => let (env, t) := c in imonad_local_env (fun _ => env) (interpret_term2_with rec t f v)).

(*
Definition interpret_kont_with (rec : kont -> term -> imonad val) (k : kont) (m : imonad val) : imonad val :=
  match k with
  | KNil => m
  | KCons c k' => interpret_clo1_with (rec k') c m
  end.
*)

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
| GTShift k t' : term1_graph K1Nil t' -> term_graph k (TShift t')
| GTReset k t' : term_graph K1Nil t' -> kont1_graph k -> term_graph k (TReset t')
| GTControl k t' : term1_graph K1Nil t' -> term_graph k (TControl t')
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

Lemma GTShift_inv k t' : term_graph k (TShift t') -> term1_graph K1Nil t'.
Proof. inversion 1; auto. Defined.

Lemma GTReset_inv1 k t' : term_graph k (TReset t') -> term_graph K1Nil t'.
Proof. inversion 1; auto. Defined.

Lemma GTReset_inv2 k t' : term_graph k (TReset t') -> kont1_graph k.
Proof. inversion 1; auto. Defined.

Lemma GTControl_inv k t' : term_graph k (TControl t') -> term1_graph K1Nil t'.
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
  | TShift t' => GTShift k (build_term1_graph_dep GK1Nil t')
  | TReset t' => GTReset (build_term_graph_dep GK1Nil t') G
  | TControl t' => GTControl k (build_term1_graph_dep GK1Nil t')
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

Fixpoint interpret_term_dep (rec : kont1 -> term -> imonad iresult) (k : kont1) (t : term) (G : term_graph k t) : imonad iresult :=
  match t return term_graph k t -> imonad iresult with
  | TAtom a => fun G => interpret_kont1_dep rec (GTAtom_inv G) (interpret_atom a)
  | TFun t' => fun G => interpret_kont1_dep rec (GTFun_inv G) (interpret_fun t')
  | TFix t' => fun G => interpret_kont1_dep rec (GTFix_inv G) (interpret_fix t')
  | TApp a1 a2 =>
      fun G =>
        let m1 := interpret_atom a1 in
        let m2 := interpret_atom a2 in
        imonad_bind m1
          (fun v => match v with
                    | VFun c => interpret_clo1_with (rec k) c m2
                    | VFix c => interpret_clo2_with (rec k) c v m2
                    | VKontS k' => imonad_throw (TypeError "") (*interpret_kont1_dep rec (GTApp_inv G) (interpret_kont_with (rec DReset) k' m2)*)
                    | VKontC k' => imonad_throw (TypeError "") (*interpret_kont_with (rec d) (kont_append k' k) m2*)
                    | _ => imonad_throw (TypeError "")
                    end)
  | TLet t1 t2 => fun G => imonad_bind imonad_ask_env (fun env => interpret_term_dep rec (GTLet_inv G env))
  | TIf a t1 t2 => fun G => interpret_if a (interpret_term_dep rec (GTIf_inv1 G)) (interpret_term_dep rec (GTIf_inv2 G))
  | TPrim1 p a => fun G => interpret_kont1_dep rec (GTPrim1_inv G) (interpret_prim1 p a)
  | TPrim2 p a1 a2 => fun G => interpret_kont1_dep rec (GTPrim2_inv G) (interpret_prim2 p a1 a2)
  | TPair a1 a2 => fun G => interpret_kont1_dep rec (GTPair_inv G) (interpret_pair a1 a2)
  | TSplit a t' => fun G => interpret_split a (interpret_term2_dep rec (GTSplit_inv G))
  | TInl a => fun G => interpret_kont1_dep rec (GTInl_inv G) (interpret_inl a)
  | TInr a => fun G => interpret_kont1_dep rec (GTInr_inv G) (interpret_inr a)
  | TCase a t1 t2 => fun G => interpret_case a (interpret_term1_dep rec (GTCase_inv1 G)) (interpret_term1_dep rec (GTCase_inv2 G))
  | TRef a => fun G => interpret_kont1_dep rec (GTRef_inv G) (interpret_ref a)
  | TGet a => fun G => interpret_kont1_dep rec (GTGet_inv G) (interpret_get a)
  | TSet a1 a2 => fun G => interpret_kont1_dep rec (GTSet_inv G) (interpret_set a1 a2)
  | TFree a => fun G => interpret_kont1_dep rec (GTFree_inv G) (interpret_free a)
  | TShift t' => fun G => imonad_pure (RBubbleS (interpret_term1_dep rec (GTShift_inv G)) (K2SHead k))
  | TReset t' =>
      fun G =>
        imonad_bind (interpret_term_dep rec (GTReset_inv1 G))
          (fun r =>
             match r with
             | RReturn v => interpret_kont1_dep rec (GTReset_inv2 G) (imonad_pure v)
             | RBubbleS rec' ks => rec' (VKontS ks)
             | RBubbleC rec' kc => imonad_pure (RBubbleC rec' (K2CSnoc kc k))
             end)
  | TControl t' => fun G => imonad_pure (RBubbleC (interpret_term1_dep rec (GTControl_inv G)) (K2CHead k))
  | TPrompt t' =>
      fun G =>
        imonad_bind (interpret_term_dep rec (GTPrompt_inv1 G))
          (fun r =>
             match r with
             | RReturn v => interpret_kont1_dep rec (GTPrompt_inv2 G) (imonad_pure v)
             | RBubbleS rec' ks => rec' (VKontS ks)
             | RBubbleC rec' kc => imonad_pure (RBubbleC rec' (K2CSnoc kc k))
             end)
  end G
with interpret_term1_dep (rec : kont1 -> term -> imonad iresult) (k : kont1) (t : term1) (G : term1_graph k t) (v : val) : imonad iresult :=
  match t return term1_graph k t -> imonad iresult with
  | T1 b t' => fun G => with_binder b v (interpret_term_dep rec (GT1_inv G))
  end G
with interpret_term2_dep (rec : kont1 -> term -> imonad iresult) (k : kont1) (t : term2) (G : term2_graph k t) (v1 v2 : val) : imonad iresult :=
  match t return term2_graph k t -> imonad iresult with
  | T2 b1 b2 t' => fun G => with_binder b1 v1 (with_binder b2 v2 (interpret_term_dep rec (GT2_inv G)))
  end G
with interpret_clo1_dep (rec : kont1 -> term -> imonad iresult) (k : kont1) (c : clo1) (G : clo1_graph k c) (m : imonad val) : imonad iresult :=
  imonad_bind m
    (fun v => match c return clo1_graph k c -> imonad iresult with
              | C1 env t => fun G => imonad_local_env (fun _ => env) (interpret_term1_dep rec (GC1_inv G) v)
              end G)
with interpret_kont1_dep (rec : kont1 -> term -> imonad iresult) (k : kont1) (G : kont1_graph k) (m : imonad val) : imonad iresult :=
  match k return kont1_graph k -> imonad iresult with
  | K1Nil => fun _ => imonad_map RReturn m
  | K1Cons c k' => fun G => interpret_clo1_dep rec (GK1Cons_inv G) m
  end G.

Unset Implicit Arguments.

Fixpoint build_kont1_graph (k : kont1) : kont1_graph k :=
  match k with
  | K1Nil => GK1Nil
  | K1Cons c k' => GK1Cons (build_clo1_graph_dep (build_kont1_graph k') c)
  end.

Definition build_term_graph (d : delim) (k : kont) (t : term) : term_graph d k t :=
  build_term_graph_dep (build_kont1_graph d k) t.

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
