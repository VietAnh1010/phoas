From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax var venv.
From shift_reset.interpreter Require Import istate ierror imonad.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition interpret_expr1_aux (go : expr -> imonad val) (e : expr1) (v : val) : imonad val :=
  let (b, e') := e in
  match b with
  | BAnon => go e'
  | BVar x => imonad_local_env (VECons x v) (go e')
  end.

Definition interpret_expr2_aux (go : expr -> imonad val) (e : expr2) (v1 v2 : val) : imonad val :=
  let (b, e') := e in
  match b with
  | BAnon => interpret_expr1_aux go e' v2
  | BVar x => imonad_local_env (VECons x v1) (interpret_expr1_aux go e' v2)
  end.

Definition interpret_let : imonad val -> (val -> imonad val) -> imonad val :=
  imonad_bind.

Definition interpret_if (a e1 e2 : imonad val) :=
  imonad_bind a
    (fun v => match v with
              | VBool b => if b then e1 else e2
              | _ => imonad_throw (TypeError "")
              end).

Definition interpret_prim1 (p : prim1) (a : imonad val) : imonad val :=
  imonad_bind a
    (fun v => match p, v with
              | P1Neg, VInt i => imonad_pure (VInt (-i))
              | P1Not, VBool b => imonad_pure (VBool (negb b))
              | _, _ => imonad_throw (TypeError "")
              end).

Definition interpret_prim2 (p : prim2) (a1 a2 : imonad val) : imonad val :=
  imonad_bind a1
    (fun v1 =>
       match p, v1 with
       | P2Add, VInt i1 =>
           imonad_bind a2
             (fun v2 => match v2 with
                        | VInt i2 => imonad_pure (VInt (i1 + i2))
                        | _ => imonad_throw (TypeError "")
                        end)
       | P2Sub, VInt i1 =>
           imonad_bind a2
             (fun v2 => match v2 with
                        | VInt i2 => imonad_pure (VInt (i1 - i2))
                        | _ => imonad_throw (TypeError "")
                        end)
       | P2Mul, VInt i1 =>
           imonad_bind a2
             (fun v2 => match v2 with
                        | VInt i2 => imonad_pure (VInt (i1 * i2))
                        | _ => imonad_throw (TypeError "")
                        end)
       | P2Div, VInt i1 =>
           imonad_bind a2
             (fun v2 => match v2 with
                        | VInt i2 => imonad_pure (VInt (i1 / i2))
                        | _ => imonad_throw (TypeError "")
                        end)
       | P2Rem, VInt i1 =>
           imonad_bind a2
             (fun v2 => match v2 with
                        | VInt i2 => imonad_pure (VInt (Z.rem i1 i2))
                        | _ => imonad_throw (TypeError "")
                        end)
       | P2And, VBool b1 =>
           imonad_bind a2
             (fun v2 => match v2 with
                        | VBool b2 => imonad_pure (VBool (b1 && b2))
                        | _ => imonad_throw (TypeError "")
                        end)
       | P2Or, VBool b1 =>
           imonad_bind a2
             (fun v2 => match v2 with
                        | VBool b2 => imonad_pure (VBool (b1 || b2))
                        | _ => imonad_throw (TypeError "")
                        end)
       | P2Xor, VBool b1 =>
           imonad_bind a2
             (fun v2 => match v2 with
                        | VBool b2 => imonad_pure (VBool (xorb b1 b2))
                        | _ => imonad_throw (TypeError "")
                        end)
       | P2Eq, _ => imonad_bind a2 (fun v2 => imonad_pure (VBool (val_eqb v1 v2)))
       | P2Lt, VInt i1 =>
           imonad_bind a2
             (fun v2 => match v2 with
                        | VInt i2 => imonad_pure (VBool (i1 <? i2))
                        | _ => imonad_throw (TypeError "")
                        end)
       | P2Le, VInt i1 =>
           imonad_bind a2
             (fun v2 => match v2 with
                        | VInt i2 => imonad_pure (VBool (i1 <=? i2))
                        | _ => imonad_throw (TypeError "")
                        end)
       | _, _ => imonad_throw (TypeError "")
       end).

Definition interpret_fun (e : expr1) : imonad val :=
  imonad_map (VFun e) imonad_ask_env.

Definition interpret_fix (e : expr2) : imonad val :=
  imonad_map (VFix e) imonad_ask_env.

Definition interpret_app (go : expr -> imonad val) (a1 a2 : imonad val) : imonad val :=
  imonad_bind a1
    (fun v1 =>
       match v1 with
       | VFun e ve => imonad_bind a2 (fun v2 => imonad_local_env (fun _ => ve) (interpret_expr1_aux go e v2))
       | VFix e ve => imonad_bind a2 (fun v2 => imonad_local_env (fun _ => ve) (interpret_expr2_aux go e v1 v2))
       | _ => imonad_throw (TypeError "")
       end).

Definition interpret_pair : imonad val -> imonad val -> imonad val :=
  imonad_lift2 VPair.

Definition interpret_fst (a : imonad val) : imonad val :=
  imonad_bind a
    (fun v => match v with
              | VPair v1 _ => imonad_pure v1
              | _ => imonad_throw (TypeError "")
              end).

Definition interpret_snd (a : imonad val) : imonad val :=
  imonad_bind a
    (fun v => match v with
              | VPair _ v2 => imonad_pure v2
              | _ => imonad_throw (TypeError "")
              end).

Definition interpret_inl : imonad val -> imonad val :=
  imonad_map VInl.

Definition interpret_inr : imonad val -> imonad val :=
  imonad_map VInr.

Definition interpret_case (a : imonad val) (e1 e2 : val -> imonad val) : imonad val :=
  imonad_bind a
    (fun v => match v with
              | VInl v' => e1 v'
              | VInr v' => e2 v'
              | _ => imonad_throw (TypeError "")
              end).

Definition interpret_ref (a : imonad val) : imonad val :=
  imonad_bind a
    (fun v =>
       imonad_bind imonad_get_state
         (fun s => match istate_ref v s with
                   | None => imonad_throw (MemoryError "")
                   | Some (l, s') => imonad_then (imonad_set_state s') (imonad_pure (VLoc l))
                   end)).

Definition interpret_get (a : imonad val) : imonad val :=
  imonad_bind a
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

Definition interpret_set (a1 a2 : imonad val) : imonad val :=
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

Definition interpret_free (a : imonad val) : imonad val :=
  imonad_bind a
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

Definition interpret_atom (a : atom) : imonad val :=
  match a with
  | AVal v => imonad_pure v
  | AVar x =>
      imonad_bind imonad_ask_env
        (fun ve => match venv_lookup x ve with
                   | None => imonad_throw (NameError "")
                   | Some v => imonad_pure v
                   end)
  end.

Definition interpret_expr_aux (go : expr -> imonad val) : expr -> imonad val :=
  fix go' e {struct e} :=
    match e with
    | EAtom a => interpret_atom a
    | ELet e1 e2 => interpret_let (go' e1) (interpret_expr1_aux go' e2)
    | EIf a e1 e2 => interpret_if (interpret_atom a) (go' e1) (go' e2)
    | EPrim1 p a => interpret_prim1 p (interpret_atom a)
    | EPrim2 p a1 a2 => interpret_prim2 p (interpret_atom a1) (interpret_atom a2)
    | EFun e' => interpret_fun e'
    | EFix e' => interpret_fix e'
    | EApp a1 a2 => interpret_app go (interpret_atom a1) (interpret_atom a2)
    | EPair a1 a2 => interpret_pair (interpret_atom a1) (interpret_atom a2)
    | EFst a => interpret_fst (interpret_atom a)
    | ESnd a => interpret_snd (interpret_atom a)
    | EInl a => interpret_inl (interpret_atom a)
    | EInr a => interpret_inr (interpret_atom a)
    | ECase a e1 e2 => interpret_case (interpret_atom a) (interpret_expr1_aux go' e1) (interpret_expr1_aux go' e2)
    | ERef a => interpret_ref (interpret_atom a)
    | EGet a => interpret_get (interpret_atom a)
    | ESet a1 a2 => interpret_set (interpret_atom a1) (interpret_atom a2)
    | EFree a => interpret_free (interpret_atom a)
    | EShift _ => imonad_throw (ControlError "shift without enclosing reset")
    | EReset e' => imonad_throw OutOfFuel
    | ECont e1 e2 => imonad_throw OutOfFuel
    end.

Fixpoint interpret_expr (fuel : nat) : expr -> imonad val :=
  interpret_expr_aux (match fuel with
                      | O => fun _ => imonad_throw OutOfFuel
                      | S fuel' => interpret_expr fuel'
                      end).

Definition run (fuel : nat) (e : expr) : (ierror + val) * istate :=
  interpret_expr fuel e VENil istate_empty.

Definition eval (fuel : nat) (e : expr) : ierror + val :=
  fst (run fuel e).

Definition exec (fuel : nat) (e : expr) : istate :=
  snd (run fuel e).
