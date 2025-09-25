From Stdlib Require Import String ZArith Lia.
From shift_reset.core Require Import syntax var env.
From shift_reset.interpreter Require Import istate ierror imonad.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition interpret_atom (a : atom) : imonad val :=
  match a with
  | AVal v => imonad_pure v
  | AVar x => imonad_bind imonad_ask_env
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
  let (t, env) := c in imonad_local_env (fun _ => env) (interpret_term1_aux go t v).

Definition interpret_clo2_aux (go : term -> imonad val) (c : clo2) (v1 v2 : val) : imonad val :=
  let (t, env) := c in imonad_local_env (fun _ => env) (interpret_term2_aux go t v1 v2).

(*
Definition interpret_kont_aux (go : kont -> term -> imonad val) (k : kont) (v : val) : imonad val :=
  match k with
  | KNil => imonad_pure v
  | KCons c k' => interpret_clo1_aux (go k') c v
  end.
*)

Definition interpret_let : imonad val -> (val -> imonad val) -> imonad val :=
  imonad_bind.

Definition interpret_if (a : atom) (t1 t2 : imonad val) :=
  imonad_bind (interpret_atom a)
    (fun v => match v with
              | VBool b => if b then t1 else t2
              | _ => imonad_throw (TypeError "")
              end).

Definition interpret_prim1 (p : prim1) (a : atom) : imonad val :=
  imonad_bind (interpret_atom a)
    (fun v => match p, v with
              | P1Neg, VInt i => imonad_pure (VInt (-i))
              | P1Not, VBool b => imonad_pure (VBool (negb b))
              | _, _ => imonad_throw (TypeError "")
              end).

Definition interpret_prim2_aux (p : prim2) (a1 a2 : imonad val) : imonad val :=
  imonad_bind a1
    (fun v1 =>
       match p, v1 with
       | P2Add, VInt i1 => imonad_bind a2
                             (fun v2 => match v2 with
                                        | VInt i2 => imonad_pure (VInt (i1 + i2))
                                        | _ => imonad_throw (TypeError "")
                                        end)
       | P2Sub, VInt i1 => imonad_bind a2
                             (fun v2 => match v2 with
                                        | VInt i2 => imonad_pure (VInt (i1 - i2))
                                        | _ => imonad_throw (TypeError "")
                                        end)
       | P2Mul, VInt i1 => imonad_bind a2
                             (fun v2 => match v2 with
                                        | VInt i2 => imonad_pure (VInt (i1 * i2))
                                        | _ => imonad_throw (TypeError "")
                                        end)
       | P2Div, VInt i1 => imonad_bind a2
                             (fun v2 => match v2 with
                                        | VInt i2 => imonad_pure (VInt (i1 / i2))
                                        | _ => imonad_throw (TypeError "")
                                        end)
       | P2Rem, VInt i1 => imonad_bind a2
                             (fun v2 => match v2 with
                                        | VInt i2 => imonad_pure (VInt (Z.rem i1 i2))
                                        | _ => imonad_throw (TypeError "")
                                        end)
       | P2And, VBool b1 => imonad_bind a2
                              (fun v2 => match v2 with
                                         | VBool b2 => imonad_pure (VBool (b1 && b2))
                                         | _ => imonad_throw (TypeError "")
                                         end)
       | P2Or, VBool b1 => imonad_bind a2
                             (fun v2 => match v2 with
                                        | VBool b2 => imonad_pure (VBool (b1 || b2))
                                        | _ => imonad_throw (TypeError "")
                                        end)
       | P2Xor, VBool b1 => imonad_bind a2
                              (fun v2 => match v2 with
                                         | VBool b2 => imonad_pure (VBool (xorb b1 b2))
                                         | _ => imonad_throw (TypeError "")
                                         end)
       | P2Eq, _ => imonad_bind a2 (fun v2 => imonad_pure (VBool (val_eqb v1 v2)))
       | P2Lt, VInt i1 => imonad_bind a2
                            (fun v2 => match v2 with
                                       | VInt i2 => imonad_pure (VBool (i1 <? i2))
                                       | _ => imonad_throw (TypeError "")
                                       end)
       | P2Le, VInt i1 => imonad_bind a2
                            (fun v2 => match v2 with
                                       | VInt i2 => imonad_pure (VBool (i1 <=? i2))
                                       | _ => imonad_throw (TypeError "")
                                       end)
       | _, _ => imonad_throw (TypeError "")
       end).

Definition interpret_prim2 (p : prim2) (a1 a2 : atom) : imonad val :=
  interpret_prim2_aux p (interpret_atom a1) (interpret_atom a2).

Definition interpret_fun (t : term1) : imonad val :=
  imonad_map (fun env => VFun (C1 t env)) imonad_ask_env.

Definition interpret_fix (t : term2) : imonad val :=
  imonad_map (fun env => VFix (C2 t env)) imonad_ask_env.

Definition interpret_app_aux (go : term -> imonad val) (a1 a2 : imonad val) : imonad val :=
  imonad_bind a1
    (fun v1 =>
       match v1 with
       | VFun c => imonad_bind a2 (interpret_clo1_aux go c)
       | VFix c => imonad_bind a2 (interpret_clo2_aux go c v1)
       | VKont k => imonad_throw (ControlError "VKont to be implemented")
       | _ => imonad_throw (TypeError "")
       end).

Definition interpret_app (go : term -> imonad val) (a1 a2 : atom) : imonad val :=
  interpret_app_aux go (interpret_atom a1) (interpret_atom a2).

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

Definition interpret_set_aux (a1 a2 : imonad val) : imonad val :=
  imonad_bind a1
    (fun v1 =>
       match v1 with
       | VLoc l =>
           imonad_bind a2
             (fun v2 =>
                imonad_bind imonad_get_state
                  (fun s =>
                     match istate_set l v2 s with
                     | None => imonad_throw (MemoryError "")
                     | Some s' => imonad_then (imonad_set_state s') (imonad_pure VUnit)
                     end))
       | _ => imonad_throw (TypeError "")
       end).

Definition interpret_set (a1 a2 : atom) : imonad val :=
  interpret_set_aux (interpret_atom a1) (interpret_atom a2).

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

Definition clo1_size (c : clo1) : nat :=
  let (t, _) := c in term1_size t.

Fixpoint kont_size (k : kont) : nat :=
  match k with
  | KNil => 0
  | KCons c k' => clo1_size c + kont_size k'
  end.

Local Open Scope nat_scope.

Definition interpret_term1_kont_aux (go : forall (t : term) (k : kont), Acc lt (term_size t + kont_size k) -> imonad val) (t : term1) (v : val) (k : kont) :
  Acc lt (term1_size t + kont_size k) -> imonad val :=
  match t with
  | T1 b t' => fun H_acc =>
                 let m := go t' k H_acc in
                 match b with
                 | BAnon => m
                 | BVar x => imonad_local_env (ECons x v) m
                 end
  end.

Definition interpret_clo1_kont_aux (go : forall (t : term) (k : kont), Acc lt (term_size t + kont_size k) -> imonad val) (c : clo1) (v : val) (k : kont) :
  Acc lt (clo1_size c + kont_size k) -> imonad val :=
  match c with C1 t env => fun H_acc => imonad_local_env (fun _ => env) (interpret_term1_kont_aux go t v k H_acc) end.

Definition interpret_kont_aux (go : forall (t : term) (k : kont), Acc lt (term_size t + kont_size k) -> imonad val) (k : kont) (m : imonad val) :
  Acc lt (kont_size k) -> imonad val :=
  match k with
  | KNil => fun _ => m
  | KCons c k' => fun H_acc => imonad_bind m (fun v => interpret_clo1_kont_aux go c v k' H_acc)
  end.

Definition interpret_kont_aux' (go : term -> kont -> imonad val) (k : kont) (m : imonad val) : imonad val :=
  match k with
  | KNil => m
  | KCons c k' => imonad_bind m (interpret_clo1_aux (fun t => go t k') c)
  end.

Definition interpret_term_kont_aux (go : term -> kont -> imonad val) (t : term) (k : kont) : imonad val.
  refine ((fix go' t k (H_acc : Acc lt (term_size t + kont_size k)) {struct H_acc} : imonad val :=
             match t return Acc lt (term_size t + kont_size k) -> imonad val with
             | TAtom a => fun H_acc => interpret_kont_aux go' k (interpret_atom a) _
             | TLet t1 t2 => fun H_acc => imonad_bind imonad_ask_env (fun env => go' t1 (KCons (C1 t2 env) k) _)
             | TIf a t1 t2 => fun H_acc => interpret_if a (go' t1 k _) (go' t2 k _)
             | TPrim1 p a => fun H_acc => interpret_kont_aux go' k (interpret_prim1 p a) _
             | TPrim2 p a1 a2 => fun H_acc => interpret_kont_aux go' k (interpret_prim2 p a1 a2) _
             | TFun t' => fun H_acc => interpret_kont_aux go' k (interpret_fun t') _
             | TFix t' => fun H_acc => interpret_kont_aux go' k (interpret_fix t') _
             | TApp a1 a2 => fun _ => interpret_app (fun t' => go t' k) a1 a2
             | TPair a1 a2 => fun H_acc => interpret_kont_aux go' k (interpret_pair a1 a2) _
             | TFst a => fun H_acc => interpret_kont_aux go' k (interpret_fst a) _
             | TSnd a => fun H_acc => interpret_kont_aux go' k (interpret_snd a) _
             | TInl a => fun H_acc => interpret_kont_aux go' k (interpret_inl a) _
             | TInr a => fun H_acc => interpret_kont_aux go' k (interpret_inr a) _
             | TCase a t1 t2 => fun H_acc => interpret_case a
                                               (fun v => interpret_term1_kont_aux go' t1 v k _)
                                               (fun v => interpret_term1_kont_aux go' t2 v k _)
             | TShift t' => fun H_acc => interpret_term1_kont_aux go' t' (VKont k) KNil _
             | TReset t' => fun H_acc => interpret_kont_aux go' k (go' t' KNil _) _
             | _ => fun _ => imonad_throw OutOfFuel
             end H_acc) t k (lt_wf _)).
  - simpl in *. apply (Acc_inv H_acc). lia.
  - simpl in *. apply (Acc_inv H_acc). lia.
  - simpl in *. apply (Acc_inv H_acc). lia.
  - simpl in *. apply (Acc_inv H_acc). lia.
  - simpl in *. apply (Acc_inv H_acc). lia.
  - simpl in *. apply (Acc_inv H_acc). lia.
  - simpl in *. apply (Acc_inv H_acc). lia.
  - simpl in *. apply (Acc_inv H_acc). lia.
  - simpl in *. apply (Acc_inv H_acc). lia.
  - simpl in *. apply (Acc_inv H_acc). lia.
  - simpl in *. apply (Acc_inv H_acc). lia.
  - simpl in *. apply (Acc_inv H_acc). lia.
  - simpl in *. apply (Acc_inv H_acc). lia.
  - simpl in *. apply (Acc_inv H_acc). lia.
  - simpl in *. apply (Acc_inv H_acc). lia.
  - simpl in *. apply (Acc_inv H_acc). lia.
  - simpl in *. apply (Acc_inv H_acc). lia.
  - simpl in *. apply (Acc_inv H_acc). lia.
Defined.

Local Close Scope nat_scope.

Definition interpret_term_kont_bot (_ : term) (_ : kont) : imonad val :=
  imonad_throw OutOfFuel.

Fixpoint interpret_term_kont (fuel : nat) (t : term) (k : kont) : imonad val :=
  match fuel with
  | O => interpret_term_kont_bot
  | S fuel' => interpret_term_kont_aux (interpret_term_kont fuel')
  end t k.

(*
Definition interpret_term_cont_aux (go : term -> imonad val) (go_cont : clo1 -> term -> imonad val) : clo1 -> term -> imonad val :=
  fix go_cont' k t {struct t} :=
    match t with
    | TAtom a => imonad_bind (interpret_atom a) (interpret_clo1_aux go k)
    | TLet t1 t2 => imonad_bind imonad_ask_env (fun env => go_cont' (C1 (compose t2 k) env) t1)
    | TIf a t1 t2 => interpret_if a (go_cont' k t1) (go_cont' k t2)
    | TPrim1 p a => imonad_bind (interpret_prim1 p a) (interpret_clo1_aux go k)
    | TPrim2 p a1 a2 => imonad_bind (interpret_prim2 p a1 a2) (interpret_clo1_aux go k)
    | TFun t' => imonad_bind (interpret_fun t') (interpret_clo1_aux go k)
    | TFix t' => imonad_bind (interpret_fix t') (interpret_clo1_aux go k)
    | TApp a1 a2 => interpret_app (go_cont k) a1 a2
    | TPair a1 a2 => imonad_bind (interpret_pair a1 a2) (interpret_clo1_aux go k)
    | TFst a => imonad_bind (interpret_fst a) (interpret_clo1_aux go k)
    | TSnd a => imonad_bind (interpret_snd a) (interpret_clo1_aux go k)
    | TInl a => imonad_bind (interpret_inl a) (interpret_clo1_aux go k)
    | TInr a => imonad_bind (interpret_inr a) (interpret_clo1_aux go k)
    | TCase a t1 t2 => interpret_case a (interpret_term1_aux (go_cont' k) t1) (interpret_term1_aux (go_cont' k) t2)
    | TShift t' => interpret_term1_aux (go_cont' identity) t' (VFun k)
    | TReset t' => imonad_bind (go_cont' identity t') (interpret_clo1_aux go k)
    | TCont t' k' => imonad_bind (go_cont' k'  t') (interpret_clo1_aux go k)
    | _ => imonad_throw OutOfFuel
    end.
*)

Definition interpret_app_aux' (go : term -> imonad val) (go_cont : term -> kont -> imonad val) (a1 a2 : imonad val) : imonad val :=
  imonad_bind a1
    (fun v1 =>
       match v1 with
       | VFun c => imonad_bind a2 (interpret_clo1_aux go c)
       | VFix c => imonad_bind a2 (interpret_clo2_aux go c v1)
       | VKont k => interpret_kont_aux' go_cont k a2
       | _ => imonad_throw (TypeError "")
       end).

Definition interpret_app' (go : term -> imonad val) (go_cont : term -> kont -> imonad val) (a1 a2 : atom) : imonad val :=
  interpret_app_aux' go go_cont (interpret_atom a1) (interpret_atom a2).

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
    | TApp a1 a2 => interpret_app' go go_kont a1 a2
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
    | TReset t' => go_kont t' KNil
    (*| TCont t' k => interpret_term_kont_aux go_kont t' k*)
    | TCont _ _ => imonad_throw (ControlError "TCont not supported!")
    end.

Definition interpret_term_bot (_ : term) : imonad val :=
  imonad_throw OutOfFuel.

Fixpoint interpret_term (fuel : nat) (t : term) : imonad val :=
  match fuel with
  | O => interpret_term_aux interpret_term_bot interpret_term_kont_bot
  | S fuel' => interpret_term_aux (interpret_term fuel') (interpret_term_kont fuel)
  end t.

Definition run (fuel : nat) (e : term) : (ierror + val) * istate :=
  interpret_term fuel e ENil istate_empty.

Definition eval (fuel : nat) (e : term) : ierror + val :=
  fst (run fuel e).

Definition exec (fuel : nat) (e : term) : istate :=
  snd (run fuel e).

Import Coerce.
Example f := TReset (TLet
                       (TPrim2 P2Mul (VInt 6) (VInt 9))
                       (T1 (Var "x")
                          (TLet
                             (TShift (T1 (Var "k") (Var "k")))
                             (T1 (Var "y") (TPrim2 P2Add (Var "x") (Var "y")))))).
Example fx := TLet f (T1 (Var "f") (TApp (Var "f") (VInt 10))).
Compute (eval 1 fx).

Example append :=
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

Fixpoint encode (xs : list Z) : val :=
  match xs with
  | nil => VInl VUnit
  | cons x xs' => VInr (VPair (VInt x) (encode xs'))
  end.

Example wrap_append v1 :=
  TReset (TLet append (T1 (Var "append") (TApp (Var "append") v1))).
Example use_append v1 v2 :=
  TLet (wrap_append v1)
    (T1 (Var "f") (TApp (Var "f") v2)).

Example append1 := use_append (encode nil) (encode (1 :: nil)).
Example append2 := use_append (encode (1 :: 2 :: 3 :: 4 :: nil)) (encode (4 :: 5 :: 6 :: 7 :: nil)).

Compute (eval 2 (wrap_append (encode (nil)))).
