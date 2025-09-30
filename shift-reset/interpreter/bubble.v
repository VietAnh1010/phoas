From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax env loc var.
From shift_reset.interpreter Require Import ierror iheap imonad.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Inductive result : Type :=
| RVal : val -> result
| RBubble : (val -> imonad result) -> kont -> result.

Fixpoint kont_append (k1 k2 : kont) : kont :=
  match k1 with
  | KNil => k2
  | KCons c k1' => KCons c (kont_append k1' k2)
  end.

Definition kont_singleton (c : clo1) : kont :=
  KCons c KNil.

(* we can refine the kont however we want, as long as we are faithful with
   its semantics *)

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

Definition unwrap_VInt_then (m : imonad val) (k : Z -> imonad result) : imonad result :=
  imonad_bind m
    (fun v => match v with
              | VInt i => k i
              | _ => imonad_throw (TypeError "")
              end).

Definition unwrap_VBool_then (m : imonad val) (k : bool -> imonad result) : imonad result :=
  imonad_bind m
    (fun v => match v with
              | VBool b => k b
              | _ => imonad_throw (TypeError "")
              end).

Definition unwrap_VLoc_then (m : imonad val) (k : loc -> imonad result) : imonad result :=
  imonad_bind m
    (fun v => match v with
              | VLoc l => k l
              | _ => imonad_throw (TypeError "")
              end).

Definition interpret_if (a : atom) (m1 m2 : imonad result) : imonad result :=
  unwrap_VBool_then (interpret_atom a) (fun b => if b then m1 else m2).

Definition interpret_i2i (f : Z -> Z) (m : imonad val) : imonad result :=
  unwrap_VInt_then m (fun i => imonad_pure (RVal (VInt (f i)))).

Definition interpret_b2b (f : bool -> bool) (m : imonad val) : imonad result :=
  unwrap_VBool_then m (fun b => imonad_pure (RVal (VBool (f b)))).

Definition interpret_prim1 (p : prim1) (a : atom) : imonad result :=
  let m := interpret_atom a in
  match p with
  | P1Neg => interpret_i2i Z.opp m
  | P1Not => interpret_b2b negb m
  end.

Definition interpret_ii2i (f : Z -> Z -> Z) (m1 m2 : imonad val) : imonad result :=
  unwrap_VInt_then m1 (fun i1 => unwrap_VInt_then m2 (fun i2 => imonad_pure (RVal (VInt (f i1 i2))))).

Definition interpret_ii2b (f : Z -> Z -> bool) (m1 m2 : imonad val) : imonad result :=
  unwrap_VInt_then m1 (fun i1 => unwrap_VInt_then m2 (fun i2 => imonad_pure (RVal (VBool (f i1 i2))))).

Definition interpret_bb2b (f : bool -> bool -> bool) (m1 m2 : imonad val) : imonad result :=
  unwrap_VBool_then m1 (fun b1 => unwrap_VBool_then m2 (fun b2 => imonad_pure (RVal (VBool (f b1 b2))))).

Definition interpret_prim2 (p : prim2) (a1 a2 : atom) : imonad result :=
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
  | P2Eq => imonad_lift2 (fun v1 v2 => RVal (VBool (val_eqb v1 v2))) m1 m2
  | P2Neq => imonad_lift2 (fun v1 v2 => RVal (VBool (val_neqb v1 v2))) m1 m2
  end.

Definition interpret_pair (a1 a2 : atom) : imonad val :=
  imonad_lift2 VPair (interpret_atom a1) (interpret_atom a2).

Definition interpret_split (a : atom) (k : val -> val -> imonad result) : imonad result :=
  imonad_bind (interpret_atom a)
    (fun v => match v with
              | VPair v1 v2 => k v1 v2
              | _ => imonad_throw (TypeError "")
              end).

Definition interpret_inl (a : atom) : imonad val :=
  imonad_map VInl (interpret_atom a).

Definition interpret_inr (a : atom) : imonad val :=
  imonad_map VInr (interpret_atom a).

Definition interpret_case (a : atom) (k1 k2 : val -> imonad result) : imonad result :=
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

Definition interpret_get (a : atom) : imonad result :=
  unwrap_VLoc_then (interpret_atom a)
    (fun l => imonad_bind imonad_get_heap
                (fun h => match iheap_get l h with
                          | None => imonad_throw (MemoryError "")
                          | Some v => imonad_pure (RVal v)
                          end)).

Definition interpret_set (a1 a2 : atom) : imonad result :=
  let m1 := interpret_atom a1 in
  let m2 := interpret_atom a2 in
  unwrap_VLoc_then m1
    (fun l => imonad_bind m2
                (fun v => imonad_bind imonad_get_heap
                            (fun h => match iheap_set l v h with
                                      | None => imonad_throw (MemoryError "")
                                      | Some h' => imonad_then (imonad_set_heap h') (imonad_pure (RVal VUnit))
                                      end))).

Definition interpret_free (a : atom) : imonad result :=
  unwrap_VLoc_then (interpret_atom a)
    (fun l => imonad_bind imonad_get_heap
                (fun h => match iheap_free l h with
                          | None => imonad_throw (MemoryError "")
                          | Some h' => imonad_then (imonad_set_heap h') (imonad_pure (RVal VUnit))
                          end)).

Definition with_binder (b : binder) (v : val) (m : imonad result) : imonad result :=
  match b with
  | BAnon => m
  | BVar x => imonad_local_env (ECons x v) m
  end.

Definition with_env (env : env) : imonad result -> imonad result :=
  imonad_local_env (fun _ => env).

Definition interpret_term1_with (rec : term -> imonad result) (t : term1) (v : val) : imonad result :=
  let (b, t') := t in with_binder b v (rec t').

Definition interpret_term2_with (rec : term -> imonad result) (t : term2) (v1 v2 : val) : imonad result :=
  let (b1, b2, t') := t in with_binder b1 v1 (with_binder b2 v2 (rec t')).

Definition interpret_clo1_with (rec : term -> imonad result) (c : clo1) (m : imonad val) : imonad result :=
  imonad_bind m (fun v => let (env, t) := c in with_env env (interpret_term1_with rec t v)).

Definition interpret_clo2_with (rec : term -> imonad result) (c : clo2) (f : val) (m : imonad val) : imonad result :=
  imonad_bind m (fun v => let (env, t) := c in with_env env (interpret_term2_with rec t f v)).

(*
Definition interpret_kont_with (rec : term -> kont -> imonad val) (k : kont) (m : imonad val) : imonad val :=
  match k with
  | KNil => m
  | KCons c k' => interpret_clo1_with (fun t => rec t k') c m
  end.
*)

Record irec : Type := IRec { run_irec : term -> imonad result }.

Definition interpret_inside_reset (m : imonad result) : imonad result :=
  imonad_bind m
    (fun r => match r with
              | RVal _ => imonad_pure r
              | RBubble f k => f (VKont k)
              end).

Fixpoint interpret_kont (rec : term -> imonad result) (k : kont) (m : imonad val) : imonad result :=
  match k with
  | KNil => imonad_map RVal m
  | KCons c k' => imonad_bind
                    (interpret_clo1_with rec c m)
                    (fun r => match r with
                              | RVal v => interpret_kont rec k' (imonad_pure v)
                              | RBubble f k'' => f (VKont (kont_append k'' k'))
                              end)
  end.

Fixpoint interpret_term_aux (rec : irec) (t : term) : imonad result :=
  match t with
  | TAtom a => imonad_map RVal (interpret_atom a)
  | TFun t' => imonad_map RVal (interpret_fun t')
  | TFix t' => imonad_map RVal (interpret_fix t')
  | TApp a1 a2 => let m1 := interpret_atom a1 in
                  let m2 := interpret_atom a2 in
                  imonad_bind m1
                    (fun v => match v with
                              | VFun c => interpret_clo1_with (run_irec rec) c m2
                              | VFix c => interpret_clo2_with (run_irec rec) c v m2
                              (*can refine the kont here back to a function, and then apply it lol *)
                              (*the function will have a shift wrap around it*)
                              | VKont k => interpret_kont (run_irec rec) k m2
                              | _ => imonad_throw (TypeError "not a fun/fix/kont")
                              end)
  | TLet t1 t2 => imonad_bind imonad_ask_env
                    (fun env =>
                       imonad_bind (interpret_term_aux rec t1)
                         (fun r => match r with
                                   | RVal v => interpret_term1_aux rec t2 v
                                   | RBubble f k => imonad_pure (RBubble f (kont_append k (kont_singleton (C1 env t2))))
                                   end))
  | TIf a t1 t2 => interpret_if a (interpret_term_aux rec t1) (interpret_term_aux rec t2)
  | TPrim1 p a => interpret_prim1 p a
  | TPrim2 p a1 a2 => interpret_prim2 p a1 a2
  | TPair a1 a2 => imonad_map RVal (interpret_pair a1 a2)
  | TSplit a t' => interpret_split a (interpret_term2_aux rec t')
  | TInl a => imonad_map RVal (interpret_inl a)
  | TInr a => imonad_map RVal (interpret_inr a)
  | TCase a t1 t2 => interpret_case a (interpret_term1_aux rec t1) (interpret_term1_aux rec t2)
  | TRef a => imonad_map RVal (interpret_ref a)
  | TGet a =>  (interpret_get a)
  | TSet a1 a2 =>  (interpret_set a1 a2)
  | TFree a =>  (interpret_free a)
  | TShift t' =>
      imonad_bind imonad_ask_env
        (fun env =>
           imonad_pure
             (RBubble
                (fun v => interpret_inside_reset (with_env env (interpret_term1_aux rec t' v)))
                KNil))
  | TReset t' => interpret_inside_reset (interpret_term_aux rec t') (* val or bubble *)
  end
with interpret_term1_aux (rec : irec) (t : term1) (v : val) : imonad result :=
  let (b, t') := t in with_binder b v (interpret_term_aux rec t')
with interpret_term2_aux (rec : irec) (t : term2) (v1 v2 : val) : imonad result :=
  let (b1, b2, t') := t in with_binder b1 v1 (with_binder b2 v2 (interpret_term_aux rec t')).

Fixpoint interpret_term (fuel : nat) (t : term) : imonad result :=
  match fuel with
  | O => imonad_throw OutOfFuel
  | S fuel' => interpret_term_aux (IRec (interpret_term fuel')) t
  end.

Definition run_term (fuel : nat) (t : term) : (ierror + result) * iheap :=
  imonad_run (interpret_term fuel t) ENil iheap_empty.

Definition eval_term (fuel : nat) (t : term) : ierror + result :=
  fst (run_term fuel t).

Definition exec_term (fuel : nat) (t : term) : iheap :=
  snd (run_term fuel t).
