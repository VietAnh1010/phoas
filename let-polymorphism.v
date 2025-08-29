Section Syntax.

  Variable tvar : Type.

  Inductive ty : Type :=
  | TyVar : tvar -> ty
  | TyLift : Type -> ty
  | TyFun : ty -> ty -> ty.

  Inductive tys : Type :=
  | TysBase : ty -> tys
  | TysForall : (tvar -> tys) -> tys.

  Variable var : tys -> Type.

  Inductive inst : tys -> ty -> Prop :=
  | InstBase : forall (t : ty), inst (TysBase t) t
  | InstForall : forall (f : tvar -> tys) (t : ty) (a : tvar), inst (f a) t -> inst (TysForall f) t.

  Inductive expr : ty -> Type :=
  | EVar : forall (s : tys) (t : ty), var s -> inst s t -> expr t
  | EConst : forall (A : Type), A -> expr (TyLift A)
  | EFun : forall (dom ran : ty), (var (TysBase dom) -> expr ran) -> expr (TyFun dom ran)
  | EApp : forall (dom ran : ty), expr (TyFun dom ran) -> expr dom -> expr ran
  | ELet : forall (s : tys) (t : ty), (forall (t' : ty), inst s t' -> expr t') -> (var s -> expr t) -> expr t.
End Syntax.

Check expr.

Axiom todo : forall (A : Type), A.
Definition tvar_basic := ty Type -> tys (ty Type).

Lemma inst_EVvar :
  inst tvar_basic
    (TysForall tvar_basic
       (fun a : tvar_basic =>
          TysBase tvar_basic
            (TyFun tvar_basic (TyVar tvar_basic a)
               (TyVar tvar_basic a))))
    (TyFun tvar_basic (TyLift tvar_basic nat)
       (TyLift tvar_basic nat)).
Proof.
  econstructor.
  try econstructor. (* cannot equate TyVar with TyLift *)
Abort.

Check (fun var =>
         ELet tvar_basic var
           (TysForall _ (fun a => TysBase _ (TyFun _ (TyVar _ a) (TyVar _ a))))
           (TyLift _ nat)
           (fun t' H_inst => todo _)
           (fun f => EApp _ _ _ _ (EVar _ _ _ _ f (todo _)) (EConst _ _ _ 1))
      ).
