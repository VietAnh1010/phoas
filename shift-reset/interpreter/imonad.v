From shift_reset.core Require Import syntax.
From shift_reset.monad Require except.
From shift_reset.monad Require Import es_monad conversions.
From shift_reset.interpreter Require Import error iheap.

Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Inductive irequest : Type :=
| IRShift : metakont -> (val -> es_monad irequest iheap val) -> irequest
| IRControl : metakont -> (val -> es_monad irequest iheap val) -> irequest
| IRShift0 : metakont -> (val -> kont -> es_monad irequest iheap val) -> irequest
| IRControl0 : metakont -> (val -> kont -> es_monad irequest iheap val) -> irequest
| IRRaise : val -> irequest
| IRPerform : metakont -> val -> irequest.

Definition irequest_to_val (r : irequest) : val :=
  match r with
  | IRShift _ _ => Undelimited_shift
  | IRControl _ _ => Undelimited_control
  | IRShift0 _ _ => Undelimited_shift0
  | IRControl0 _ _ => Undelimited_control0
  | IRRaise v => v
  | IRPerform _ v => Unhandled_effect v
  end.

Definition iv_monad : Type -> Type := except.t val.
Definition ivh_monad : Type -> Type := es_monad val iheap.
Definition irh_monad : Type -> Type := es_monad irequest iheap.

Definition ivh_monad_to_irh_monad {A} : ivh_monad A -> irh_monad A :=
  with_except IRRaise.

Definition irh_monad_to_ivh_monad {A} : irh_monad A -> ivh_monad A :=
  with_except irequest_to_val.

Definition iv_monad_to_ivh_monad {A} : iv_monad A -> ivh_monad A :=
  except_to_es_monad.

Definition iv_monad_to_irh_monad {A} (m : except.t val A) : irh_monad A :=
  except_to_es_monad (except.with_except IRRaise m).
