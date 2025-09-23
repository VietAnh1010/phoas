From Stdlib Require Import String.
From shift_reset.core Require Import syntax.
From shift_reset.interpreter Require Import istate ierror imonad.

Local Open Scope string_scope.

Definition interpret_prim1 (p : prim1) (v : val) : imonad val :=
  match p, v with
  | P1Neg, VInt i => imonad_pure v
  | P1Not, VBool b => imonad_pure v
  | _, _ => imonad_throw (Stuck "type error")
  end.

Definition interpret_prim2 (p : prim2) (v1 v2 : val) : imonad val :=
  match p, v1, v2 with
  | _, _, _ => imonad_throw (Stuck "type error")
  end.

Definition interpret_fst (v : val) : imonad val :=
  match v with
  | VPair v1 _ => imonad_pure v1
  | _ => imonad_throw (Stuck "type error")
  end.

Definition interpret_snd (v : val) : imonad val :=
  match v with
  | VPair _ v2 => imonad_pure v2
  | _ => imonad_throw (Stuck "type error")
  end.

Definition interpret_ref (v : val) : imonad val :=
  imonad_bind imonad_get_state
    (fun s =>
       match istate_ref v s with
       | None => imonad_throw (Stuck "")
       | Some (l, s) => imonad_bind (imonad_set_state s) (fun _ => imonad_pure (VLoc l))
       end).

Definition interpret_get (v : val) : imonad val :=
  match v with
  | VLoc l =>
      imonad_bind imonad_get_state
        (fun s =>
           match istate_get l s with
           | None => imonad_throw (Stuck "")
           | Some v => imonad_pure v
           end)
  | _ => imonad_throw (Stuck "")
  end.

Fixpoint interpret_expr (fuel : nat) : expr -> imonad val :=
  fix atom_go a :=
    match a with
    | AVal v => imonad_pure v
    | AVar x => imonad_throw OutOfFuel
    end
with
expr_go e :=
  match e with
  | EAtom a => atom_go a
  | ELet e1 e2 => imonad_bind (expr_go e1) (expr1_go e2)
  | EIf a e1 e2 => imonad_throw OutOfFuel
  | EPrim1 p a => imonad_bind (atom_go a) (interpret_prim1 p)
  | EPrim2 p a1 a2 => imonad_bind (atom_go a1) (fun v1 => imonad_bind (atom_go a2) (interpret_prim2 p v1))
  | EFun e' => imonad_map (fun ve => VFun ve e') imonad_ask_env
  | EFix e' => imonad_map (fun ve => VFix ve e') imonad_ask_env
  | EApp a1 a2 => imonad_throw OutOfFuel
  | EPair a1 a2 => imonad_lift2 VPair (atom_go a1) (atom_go a2)
  | EFst a => imonad_bind (atom_go a) interpret_fst
  | ESnd a => imonad_bind (atom_go a) interpret_snd
  | EInl a => imonad_map VInl (atom_go a)
  | EInr a => imonad_map VInr (atom_go a)
  | ECase a e1 e2 => imonad_throw OutOfFuel
  | ERef a => imonad_bind (atom_go a) interpret_ref
  | EGet a => imonad_bind (atom_go a) interpret_get
  | ESet a1 a2 => imonad_throw OutOfFuel
  | EFree a => imonad_throw OutOfFuel
  | EShift _ => imonad_throw (Stuck "shift without enclosing reset")
  | EReset e' => imonad_throw OutOfFuel
  | ECont e1 e2 => imonad_throw OutOfFuel
  end
with
expr1_go e v :=
  match e with
  | E1Bind b e' =>
      match b with
      | BAnon => expr_go e'
      | BVar x => imonad_local_env (VECons x v) (expr_go e')
      end
  end
    for expr_go.
