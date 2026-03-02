Set Implicit Arguments.

Section Syntax.
  Variable var : Type.

  Inductive term : Type :=
  | TVar : var -> term
  | TApp : term -> term -> term
  | TAbs : (var -> term) -> term.
End Syntax.

Arguments TVar [var].
Arguments TApp [var].
Arguments TAbs [var].

Definition Term := forall var, term var.

Definition t_id : Term := fun _ => TAbs (fun x => TVar x).
Definition t_app : Term := fun _ => TAbs (fun f => TAbs (fun x => TApp (TVar f) (TVar x))).

Fixpoint count_vars (t : term unit) : nat :=
  match t with
  | TVar _ => 1
  | TApp t1 t2 => count_vars t1 + count_vars t2
  | TAbs f => count_vars (f tt)
  end.

Definition CountVars (t : Term) : nat :=
  count_vars (t unit).

Compute (count_vars (t_id unit)).
Compute (CountVars t_id).
Compute (CountVars t_app).

Fixpoint can_eta_top_level' (t : term bool) : bool :=
  match t with
  | TVar b => b
  | TApp t1 t2 => can_eta_top_level' t1 && can_eta_top_level' t2
  | TAbs f => can_eta_top_level' (f true)
  end.

Definition can_eta_top_level (t : term bool) : bool :=
  match t with
  | TAbs f => match f false with
              | TApp t (TVar false) => can_eta_top_level' t
              | _ => false
              end
  | _ => false
  end.

Definition CanEtaTopLevel (t : Term) : bool :=
  can_eta_top_level (t bool).

Compute (CanEtaTopLevel t_id).
Compute (CanEtaTopLevel t_app).

Definition t_etable : Term :=
  fun _ => TAbs (fun x => TApp (t_id _) (TVar x)).

Compute (CanEtaTopLevel t_etable).

(* term with 1 free variable *)
Definition Term1 := forall var, var -> term var.

Fixpoint subst (var : Type) (t : term (term var)) : term var :=
  match t with
  | TVar t' => t'
  | TApp t1 t2 => TApp (subst t1) (subst t2)
  | TAbs f => TAbs (fun x : var => subst (f (TVar x)))
  end.

Definition Subst (t1 : Term1) (t2 : Term) : Term :=
  fun var => subst (t1 (term var) (t2 var)).
