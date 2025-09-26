From Stdlib Require Import String ZArith Lia.
From shift_reset.core Require Import syntax var env.
From shift_reset.interpreter Require Import istate ierror imonad.

Local Open Scope string_scope.

Definition interpret_atom (a : atom) : imonad val :=
  match a with
  | AUnit => imonad_pure VUnit
  | AInt i => imonad_pure (VInt i)
  | ABool b => imonad_pure (VBool b)
  | AVar x =>
      imonad_bind imonad_ask_env
        (fun env => match env_lookup x env with
                    | None => imonad_throw (NameError "")
                    | Some v => imonad_pure v
                    end)
  end.

Definition interpret_term1_aux (go : term -> imonad val) (t : term1) (v : val) : imonad val :=
  let (b, t') := t in
  match b with
  | BAnon => go t'
  | BVar x => imonad_local_env (ECons x v) (go t')
  end.

Definition interpret_term2_aux (go : term -> imonad val) (t : term2) (v1 v2 : val) : imonad val :=
  let (b, t') := t in
  match b with
  | BAnon => interpret_term1_aux go t' v2
  | BVar x => imonad_local_env (ECons x v1) (interpret_term1_aux go t' v2)
  end.

Definition interpret_clo1_aux (go : term -> imonad val) (c : clo1) (v : val) : imonad val :=
  let (env, t) := c in imonad_local_env (fun _ => env) (interpret_term1_aux go t v).

Definition interpret_clo2_aux (go : term -> imonad val) (c : clo2) (v1 v2 : val) : imonad val :=
  let (env, t) := c in imonad_local_env (fun _ => env) (interpret_term2_aux go t v1 v2).

Definition interpret_if (a : atom) (m1 m2 : imonad val) :=
  imonad_bind (interpret_atom a)
    (fun v => match v with
              | VBool b => if b then m1 else m2
              | _ => imonad_throw (TypeError "")
              end).

Local Open Scope Z_scope.

Definition interpret_prim1 (p : prim1) (a : atom) : imonad val :=
  imonad_bind (interpret_atom a)
    (fun v => match p, v with
              | P1Neg, VInt i => imonad_pure (VInt (-i))
              | P1Not, VBool b => imonad_pure (VBool (negb b))
              | _, _ => imonad_throw (TypeError "")
              end).

Definition interpret_prim2 (p : prim2) (a1 a2 : atom) : imonad val :=
  let m1 := interpret_atom a1 in
  let m2 := interpret_atom a2 in
  imonad_bind m1
    (fun v1 =>
       match p, v1 with
       | P2Add, VInt i1 =>
           imonad_bind m2
             (fun v2 => match v2 with
                        | VInt i2 => imonad_pure (VInt (i1 + i2))
                        | _ => imonad_throw (TypeError "")
                        end)
       | P2Sub, VInt i1 =>
           imonad_bind m2
             (fun v2 => match v2 with
                        | VInt i2 => imonad_pure (VInt (i1 - i2))
                        | _ => imonad_throw (TypeError "")
                        end)
       | P2Mul, VInt i1 =>
           imonad_bind m2
             (fun v2 => match v2 with
                        | VInt i2 => imonad_pure (VInt (i1 * i2))
                        | _ => imonad_throw (TypeError "")
                        end)
       | P2Div, VInt i1 =>
           imonad_bind m2
             (fun v2 => match v2 with
                        | VInt i2 => imonad_pure (VInt (i1 / i2))
                        | _ => imonad_throw (TypeError "")
                        end)
       | P2Rem, VInt i1 =>
           imonad_bind m2
             (fun v2 => match v2 with
                        | VInt i2 => imonad_pure (VInt (Z.rem i1 i2))
                        | _ => imonad_throw (TypeError "")
                        end)
       | P2Lt, VInt i1 =>
           imonad_bind m2
             (fun v2 => match v2 with
                        | VInt i2 => imonad_pure (VBool (i1 <? i2))
                        | _ => imonad_throw (TypeError "")
                        end)
       | P2Le, VInt i1 =>
           imonad_bind m2
             (fun v2 => match v2 with
                        | VInt i2 => imonad_pure (VBool (i1 <=? i2))
                        | _ => imonad_throw (TypeError "")
                        end)
       | P2And, VBool b1 =>
           imonad_bind m2
             (fun v2 => match v2 with
                        | VBool b2 => imonad_pure (VBool (b1 && b2))
                        | _ => imonad_throw (TypeError "")
                        end)
       | P2Or, VBool b1 =>
           imonad_bind m2
             (fun v2 => match v2 with
                        | VBool b2 => imonad_pure (VBool (b1 || b2))
                        | _ => imonad_throw (TypeError "")
                        end)
       | P2Xor, VBool b1 =>
           imonad_bind m2
             (fun v2 => match v2 with
                        | VBool b2 => imonad_pure (VBool (xorb b1 b2))
                        | _ => imonad_throw (TypeError "")
                        end)
       | P2Eq, _ => imonad_bind m2 (fun v2 => imonad_pure (VBool (val_eqb v1 v2)))
       | P2Neq, _ => imonad_bind m2 (fun v2 => imonad_pure (VBool (val_neqb v1 v2)))
       | _, _ => imonad_throw (TypeError "")
       end).

Local Close Scope Z_scope.

Definition interpret_fun (t : term1) : imonad val :=
  imonad_map (fun env => VFun (C1 env t)) imonad_ask_env.

Definition interpret_fix (t : term2) : imonad val :=
  imonad_map (fun env => VFix (C2 env t)) imonad_ask_env.

Definition interpret_pair (a1 a2 : atom) : imonad val :=
  imonad_lift2 VPair (interpret_atom a1) (interpret_atom a2).

Definition interpret_fst (a : atom) : imonad val :=
  imonad_bind (interpret_atom a)
    (fun v => match v with
              | VPair v1 _ => imonad_pure v1
              | _ => imonad_throw (TypeError "")
              end).

Definition interpret_snd (a : atom) : imonad val :=
  imonad_bind (interpret_atom a)
    (fun v => match v with
              | VPair _ v2 => imonad_pure v2
              | _ => imonad_throw (TypeError "")
              end).

Definition interpret_inl (a : atom) : imonad val :=
  imonad_map VInl (interpret_atom a).

Definition interpret_inr (a : atom) : imonad val :=
  imonad_map VInr (interpret_atom a).

Definition interpret_case (a : atom) (t1 t2 : val -> imonad val) : imonad val :=
  imonad_bind (interpret_atom a)
    (fun v => match v with
              | VInl v' => t1 v'
              | VInr v' => t2 v'
              | _ => imonad_throw (TypeError "")
              end).

Definition interpret_ref (a : atom) : imonad val :=
  imonad_bind (interpret_atom a)
    (fun v =>
       imonad_bind imonad_get_state
         (fun s =>
            match istate_ref v s with
            | None => imonad_throw (MemoryError "")
            | Some (l, s') => imonad_then (imonad_set_state s') (imonad_pure (VLoc l))
            end)).

Definition interpret_get (a : atom) : imonad val :=
  imonad_bind (interpret_atom a)
    (fun v =>
       match v with
       | VLoc l =>
           imonad_bind imonad_get_state
             (fun s =>
                match istate_get l s with
                | None => imonad_throw (MemoryError "")
                | Some v => imonad_pure v
                end)
       | _ => imonad_throw (TypeError "")
       end).

Definition interpret_set (a1 a2 : atom) : imonad val :=
  let m1 := interpret_atom a1 in
  let m2 := interpret_atom a2 in
  imonad_bind m1
    (fun v1 =>
       match v1 with
       | VLoc l =>
           imonad_bind m2
             (fun v2 =>
                imonad_bind imonad_get_state
                  (fun s =>
                     match istate_set l v2 s with
                     | None => imonad_throw (MemoryError "")
                     | Some s' => imonad_then (imonad_set_state s') (imonad_pure VUnit)
                     end))
       | _ => imonad_throw (TypeError "")
       end).

Definition interpret_free (a : atom) : imonad val :=
  imonad_bind (interpret_atom a)
    (fun v =>
       match v with
       | VLoc l =>
           imonad_bind imonad_get_state
             (fun s =>
                match istate_free l s with
                | None => imonad_throw (MemoryError "")
                | Some s' => imonad_then (imonad_set_state s') (imonad_pure VUnit)
                end)
       | _ => imonad_throw (TypeError "")
       end).

Fixpoint term_size (t : term) : nat :=
  match t with
  | TLet t1 t2 => S (term_size t1 + term1_size t2)
  | TIf _ t1 t2 => S (Nat.max (term_size t1) (term_size t2))
  | TShift t' => S (term1_size t')
  | TReset t' => S (term_size t')
  | TCase _ t1 t2 => S (Nat.max (term1_size t1) (term1_size t2))
  | _ => 1
  end
with term1_size (t : term1) : nat := let (_, t') := t in term_size t'.

Definition clo1_size (c : clo1) : nat := let (_, t) := c in term1_size t.

Fixpoint kont_size (k : kont) : nat :=
  match k with
  | KNil => 0
  | KCons c k' => clo1_size c + kont_size k'
  end.

Local Open Scope nat_scope.

Section interpret_kont.
  Context (go : forall (t : term) (k : kont), Acc lt (term_size t + kont_size k) -> imonad val).

  Definition interpret_term1_kont_aux (t : term1) (k : kont) (H_acc : Acc lt (term1_size t + kont_size k)) (v : val) : imonad val :=
    match t return Acc lt (term1_size t + kont_size k) -> imonad val with
    | T1 b t' => fun H_acc =>
                   let m := go t' k H_acc in
                   match b with
                   | BAnon => m
                   | BVar x => imonad_local_env (ECons x v) m
                   end
    end H_acc.

  Definition interpret_clo1_kont_aux (c : clo1) (k : kont) (H_acc : Acc lt (clo1_size c + kont_size k)) (v : val) : imonad val :=
    match c return Acc lt (clo1_size c + kont_size k) -> imonad val with
    | C1 env t => fun H_acc => imonad_local_env (fun _ => env) (interpret_term1_kont_aux t k H_acc v)
    end H_acc.

  Definition interpret_kont_aux (k : kont) (H_acc : Acc lt (kont_size k)) (m : imonad val) : imonad val :=
    match k return Acc lt (kont_size k) -> imonad val with
    | KNil => fun _ => m
    | KCons c k' => fun H_acc => imonad_bind m (interpret_clo1_kont_aux c k' H_acc)
    end H_acc.
End interpret_kont.

Definition interpret_kont (go : term -> kont -> imonad val) (k : kont) (m : imonad val) : imonad val :=
  match k with
  | KNil => m
  | KCons c k' => imonad_bind m (interpret_clo1_aux (fun t => go t k') c)
  end.

Lemma Acc_inv_succ (n : nat) (H_acc : Acc lt (S n)) : Acc lt n.
Proof.
  apply (Acc_inv H_acc).
  exact (Nat.lt_succ_diag_r n).
Defined.

Lemma Acc_inv_succ_add (m n : nat) (H_acc : Acc lt (S (m + n))) : Acc lt n.
Proof.
  apply (Acc_inv H_acc).
  rewrite -> Nat.lt_succ_r.
  exact (Nat.le_add_l n m).
Defined.

Lemma Acc_inv_succ_add_max_l (n m p : nat) (H_acc : Acc lt (S (Nat.max n m + p))) : Acc lt (n + p).
Proof.
  apply (Acc_inv H_acc).
  rewrite -> Nat.lt_succ_r.
  rewrite <- Nat.add_le_mono_r.
  exact (Nat.le_max_l _ _).
Defined.

Lemma Acc_inv_succ_add_max_r (n m p : nat) (H_acc : Acc lt (S (Nat.max n m + p))) : Acc lt (m + p).
Proof.
  apply (Acc_inv H_acc).
  rewrite -> Nat.lt_succ_r.
  rewrite <- Nat.add_le_mono_r.
  exact (Nat.le_max_r _ _).
Defined.

Lemma Acc_inv_succ_add0 (m n : nat) (H_acc : Acc lt (S (m + n))) : Acc lt (m + 0).
Proof.
  apply (Acc_inv H_acc).
  rewrite -> Nat.add_0_r.
  rewrite -> Nat.lt_succ_r.
  exact (Nat.le_add_r m n).
Defined.

(*
Definition interpret_term_kont_aux (go : term -> kont -> imonad val) (t : term) (k : kont) : imonad val.
  refine
    ((fix go' t k (H_acc : Acc lt (term_size t + kont_size k)) {struct H_acc} : imonad val :=
        match t return Acc lt (term_size t + kont_size k) -> imonad val with
        | TAtom a => fun H_acc => interpret_kont_aux go' k _ (interpret_atom a)
        | TLet t1 t2 => fun H_acc => imonad_bind imonad_ask_env (fun env => go' t1 (KCons (C1 env t2) k) _)
        | TIf a t1 t2 => fun H_acc => interpret_if a (go' t1 k _) (go' t2 k _)
        | TPrim1 p a => fun H_acc => interpret_kont_aux go' k _ (interpret_prim1 p a)
        | TPrim2 p a1 a2 => fun H_acc => interpret_kont_aux go' k _ (interpret_prim2 p a1 a2)
        | TFun t' => fun H_acc => interpret_kont_aux go' k _ (interpret_fun t')
        | TFix t' => fun H_acc => interpret_kont_aux go' k _ (interpret_fix t')
        | TApp a1 a2 => fun H_acc =>
                          let m1 := interpret_atom a1 in
                          let m2 := interpret_atom a2 in
                          imonad_bind m1
                            (fun v1 =>
                               match v1 with
                               | VFun c => imonad_bind m2 (interpret_clo1_aux (fun t' => go t' k) c)
                               | VFix c => imonad_bind m2 (interpret_clo2_aux (fun t' => go t' k) c v1)
                               | VKont k' => interpret_kont_aux go' k _ (interpret_kont go k'  m2)
                               | _ => imonad_throw (TypeError "")
                               end)
        | TPair a1 a2 => fun H_acc => interpret_kont_aux go' k _ (interpret_pair a1 a2)
        | TFst a => fun H_acc => interpret_kont_aux go' k _ (interpret_fst a)
        | TSnd a => fun H_acc => interpret_kont_aux go' k _ (interpret_snd a)
        | TInl a => fun H_acc => interpret_kont_aux go' k _ (interpret_inl a)
        | TInr a => fun H_acc => interpret_kont_aux go' k _ (interpret_inr a)
        | TCase a t1 t2 => fun H_acc => interpret_case a (interpret_term1_kont_aux go' t1 k _) (interpret_term1_kont_aux go' t2 k _)
        | TRef a => fun H_acc => interpret_kont_aux go' k _ (interpret_ref a)
        | TGet a => fun H_acc => interpret_kont_aux go' k _ (interpret_get a)
        | TSet a1 a2 => fun H_acc => interpret_kont_aux go' k _ (interpret_set a1 a2)
        | TFree a => fun H_acc => interpret_kont_aux go' k _ (interpret_free a)
        | TShift t' => fun H_acc => interpret_term1_kont_aux go' t' KNil _ (VKont k)
        | TReset t' => fun H_acc => interpret_kont_aux go' k _ (go' t' KNil _)
        end H_acc) t k (lt_wf _)).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. apply (Acc_inv H_acc). lia.
  - simpl in *. exact (Acc_inv_succ_add_max_l _ _ _ H_acc).
  - simpl in *. exact (Acc_inv_succ_add_max_r _ _ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ_add_max_l _ _ _ H_acc).
  - simpl in *. exact (Acc_inv_succ_add_max_r _ _ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ_add0 _ _ H_acc).
  - simpl in *. exact (Acc_inv_succ_add _ _ H_acc).
  - simpl in *. exact (Acc_inv_succ_add0 _ _ H_acc).
Defined.
*)

Inductive tree :=
| Nat : nat -> tree
| Plus : tree -> tree -> tree.

Fixpoint tree_size' t acc := match t with Nat _ => S acc | Plus t1 t2 => S (tree_size' t1 (tree_size' t2 acc)) end.
Definition tree_size'' t := tree_size' t 0.
Fixpoint tree_size t := match t with Nat _ => 1 | Plus t1 t2 => S (tree_size t1 + tree_size t2) end.
Fixpoint list_size ts := match ts with nil => 0 | cons t ts' => tree_size'' t + list_size ts' end.

Axiom equiv : forall t, tree_size'' t = tree_size t.
Axiom equiv' : forall t acc, tree_size' t acc = tree_size t + acc.

From Stdlib Require Import FunInd Recdef Program.

Program Fixpoint sum_tree' (ts : list tree) (acc : nat) {measure (list_size ts)} :=
  match ts with
  | nil => acc
  | cons t ts' =>
      match t with
      | Nat n => sum_tree' ts' (n + acc)
      | Plus l r => sum_tree' (cons l (cons r ts')) acc
      end
  end.
Next Obligation.
  simpl.
  rewrite ->! equiv.
  rewrite ->! equiv'.
  lia.
Qed.

Definition sum_tree t := sum_tree' (cons t nil) 0.

Fixpoint sum_t' t acc :=
  match t with
  | Nat n => n + acc
  | Plus l r => sum_t' r (sum_t' l acc)
  end.

Definition sum_t t := sum_t' t 0.

Print sum_tree'_func.

Fixpoint gen_large_tree (xs : list nat) :=
  match xs with
  | nil => Nat 1
  | cons x xs' => Plus (gen_large_tree xs') (Nat 1)
  end.

Definition large := gen_large_tree (ListDef.seq 0 2000).

Time Compute (sum_t large).
Time Compute (sum_tree large).



(*
Section foo.
Context (go : term -> kont -> imonad val).

Program Fixpoint go' (t : term) (k : kont) {measure (term_size t + kont_size k)} : imonad val :=
  match t with
  | TAtom a => interpret_kont_aux go' k _ (interpret_atom a)
  | TLet t1 t2 => fun H_acc => imonad_bind imonad_ask_env (fun env => go' t1 (KCons (C1 env t2) k) _)
  (*
  | TIf a t1 t2 => fun H_acc => interpret_if a (go' t1 k _) (go' t2 k _)
  | TPrim1 p a => fun H_acc => interpret_kont_aux go' k _ (interpret_prim1 p a)
  | TPrim2 p a1 a2 => fun H_acc => interpret_kont_aux go' k _ (interpret_prim2 p a1 a2)
  | TFun t' => fun H_acc => interpret_kont_aux go' k _ (interpret_fun t')
  | TFix t' => fun H_acc => interpret_kont_aux go' k _ (interpret_fix t')
  | TApp a1 a2 => fun H_acc =>
                    let m1 := interpret_atom a1 in
                    let m2 := interpret_atom a2 in
                    imonad_bind m1
                      (fun v1 =>
                         match v1 with
                         | VFun c => imonad_bind m2 (interpret_clo1_aux (fun t' => go t' k) c)
                         | VFix c => imonad_bind m2 (interpret_clo2_aux (fun t' => go t' k) c v1)
                         | VKont k' => interpret_kont_aux go' k _ (interpret_kont go k'  m2)
                         | _ => imonad_throw (TypeError "")
                         end)*)
  | TPair a1 a2 => fun H_acc => interpret_kont_aux go' k _ (interpret_pair a1 a2)
  | TFst a => fun H_acc => interpret_kont_aux go' k _ (interpret_fst a)
  | TSnd a => fun H_acc => interpret_kont_aux go' k _ (interpret_snd a)
  | TInl a => fun H_acc => interpret_kont_aux go' k _ (interpret_inl a)
  | TInr a => fun H_acc => interpret_kont_aux go' k _ (interpret_inr a)
  | TCase a t1 t2 => fun H_acc => interpret_case a (interpret_term1_kont_aux go' t1 k _) (interpret_term1_kont_aux go' t2 k _)
  | TRef a => fun H_acc => interpret_kont_aux go' k _ (interpret_ref a)
  | TGet a => fun H_acc => interpret_kont_aux go' k _ (interpret_get a)
  | TSet a1 a2 => fun H_acc => interpret_kont_aux go' k _ (interpret_set a1 a2)
  | TFree a => fun H_acc => interpret_kont_aux go' k _ (interpret_free a)
  | TShift t' => fun H_acc => interpret_term1_kont_aux go' t' KNil _ (VKont k)
  | TReset t' => fun H_acc => interpret_kont_aux go' k _ (go' t' KNil _)
  end.
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. apply (Acc_inv H_acc). lia.
  - simpl in *. exact (Acc_inv_succ_add_max_l _ _ _ H_acc).
  - simpl in *. exact (Acc_inv_succ_add_max_r _ _ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ_add_max_l _ _ _ H_acc).
  - simpl in *. exact (Acc_inv_succ_add_max_r _ _ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ _ H_acc).
  - simpl in *. exact (Acc_inv_succ_add0 _ _ H_acc).
  - simpl in *. exact (Acc_inv_succ_add _ _ H_acc).
  - simpl in *. exact (Acc_inv_succ_add0 _ _ H_acc).
Defined.
*)
Local Close Scope nat_scope.

Fixpoint interpret_term_kont (fuel : nat) (t : term) (k : kont) : imonad val :=
  match fuel with
  | O => imonad_throw OutOfFuel
  | S fuel' => interpret_term_kont_aux (interpret_term_kont fuel') t k
  end.

Definition interpret_term_aux (go : term -> imonad val) (go_kont : term -> kont -> imonad val) : term -> imonad val :=
  fix go' t {struct t} :=
    match t with
    | TAtom a => interpret_atom a
    | TLet t1 t2 => imonad_bind (go' t1) (interpret_term1_aux go' t2)
    | TIf a t1 t2 => interpret_if a (go' t1) (go' t2)
    | TPrim1 p a => interpret_prim1 p a
    | TPrim2 p a1 a2 => interpret_prim2 p a1 a2
    | TFun t' => interpret_fun t'
    | TFix t' => interpret_fix t'
    | TApp a1 a2 => let m1 := interpret_atom a1 in
                    let m2 := interpret_atom a2 in
                    imonad_bind m1
                      (fun v1 =>
                         match v1 with
                         | VFun c => imonad_bind m2 (interpret_clo1_aux go c)
                         | VFix c => imonad_bind m2 (interpret_clo2_aux go c v1)
                         | VKont k => interpret_kont go_kont k m2
                         | _ => imonad_throw (TypeError "")
                         end)
    | TPair a1 a2 => interpret_pair a1 a2
    | TFst a => interpret_fst a
    | TSnd a => interpret_snd a
    | TInl a => interpret_inl a
    | TInr a => interpret_inr a
    | TCase a t1 t2 => interpret_case a (interpret_term1_aux go' t1) (interpret_term1_aux go' t2)
    | TRef a => interpret_ref a
    | TGet a => interpret_get a
    | TSet a1 a2 => interpret_set a1 a2
    | TFree a => interpret_free a
    | TShift _ => imonad_throw (ControlError "shift without enclosing reset")
    | TReset t' => interpret_term_kont_aux go_kont t' KNil
    end.

Fixpoint interpret_term (fuel : nat) (t : term) : imonad val :=
  match fuel with
  | O => imonad_throw OutOfFuel
  | S fuel' => interpret_term_aux (interpret_term fuel') (interpret_term_kont fuel') t
  end.

Definition run (fuel : nat) (e : term) : (ierror + val) * istate :=
  interpret_term fuel e ENil istate_empty.

Definition eval (fuel : nat) (e : term) : ierror + val :=
  fst (run fuel e).

Definition exec (fuel : nat) (e : term) : istate :=
  snd (run fuel e).

Import Coerce.
Local Open Scope Z_scope.
Example f := TReset (TLet
                       (TPrim2 P2Mul 6 9)
                       (T1 (Var "x")
                          (TLet
                             (TShift (T1 (Var "k") (Var "k")))
                             (T1 (Var "y") (TPrim2 P2Add (Var "x") (Var "y")))))).
Example fx := TLet f (T1 (Var "f") (TApp (Var "f") 10)).
Compute (eval 2 fx).

Example append_aux :=
  TFix
    (T2 (Var "f")
       (T1 (Var "xs")
          (TCase (Var "xs")
             (T1 BAnon (TShift (T1 (Var "k") (Var "k"))))
             (T1 (Var "p")
                (TLet
                   (TFst (Var "p"))
                   (T1 (Var "x")
                      (TLet
                         (TSnd (Var "p"))
                         (T1 (Var "xs'")
                            (TLet
                               (TApp (Var "f") (Var "xs'"))
                               (T1 (Var "r")
                                  (TLet
                                     (TPair (Var "x") (Var "r"))
                                     (T1 (Var "r'") (TInr (Var "r'")))))))))))))).

Fixpoint encode (xs : list Z) : term :=
  match xs with
  | nil => TInl AUnit
  | cons x xs' => TLet (encode xs') (T1 (Var "xs'") (TLet (TPair x (Var "xs'")) (T1 (Var "xs") (TInr (Var "xs")))))
  end.

Import List.
Import ListNotations.

Example append1 xs :=
  TLet xs (T1 (Var "xs") (TReset (TLet append_aux (T1 (Var "append_aux") (TApp (Var "append_aux") (Var "xs")))))).

Example append2 xs ys :=
  TLet ys (T1 (Var "ys") (TLet (append1 xs) (T1 (Var "append1") (TApp (Var "append1") (Var "ys"))))).

Example ex1_aux := append1 (encode nil).
Example ex1 := append2 (encode nil) (encode (1 :: nil)).
Example ex2 := append2 (encode (List.map (fun n => Z.of_nat n) (ListDef.seq 0 1000))) (encode nil).

Example append_direct :=
  TFix
    (T2 (Var "f")
       (T1 (Var "xs")
          (TFun
             (T1 (Var "ys")
                (TCase (Var "xs")
                   (T1 BAnon (Var "ys"))
                   (T1 (Var "p")
                      (TLet
                         (TFst (Var "p"))
                         (T1 (Var "x")
                            (TLet
                               (TSnd (Var "p"))
                               (T1 (Var "xs'")
                                  (TLet
                                     (TApp (Var "f") (Var "xs'"))
                                     (T1 (Var "f")
                                        (TLet
                                           (TApp (Var "f") (Var "ys"))
                                           (T1 (Var "r")
                                              (TLet
                                                 (TPair (Var "x") (Var "r"))
                                                 (T1 (Var "r'") (TInr (Var "r'")))))))))))))))))).

Example append xs ys :=
  TLet xs
    (T1 (Var "xs")
       (TLet ys
          (T1 (Var "ys")
             (TLet append_direct
                (T1 (Var "append_aux")
                   (TLet (TApp (Var "append_aux") (Var "xs"))
                      (T1 (Var "f") (TApp (Var "f") (Var "ys"))))))))).

Definition xs := encode (List.map (fun n => Z.of_nat n) (ListDef.seq 0 1000)).

Example ex3 := append xs (encode nil).

Compute (eval 10 ex1_aux).
Time Compute (eval 10 ex1).
Time Compute (interpret_term 1000 xs ENil istate_empty).
