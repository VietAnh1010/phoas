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
| IRRaise : exn -> irequest
| IRPerform : metakont -> eff -> irequest.

Definition irequest_to_exn (r : irequest) : exn :=
  match r with
  | IRShift _ _ => Undelimited_shift
  | IRControl _ _ => Undelimited_control
  | IRShift0 _ _ => Undelimited_shift0
  | IRControl0 _ _ => Undelimited_control0
  | IRRaise x => x
  | IRPerform _ f => Unhandled_effect f
  end.

Definition ixmonad : Type -> Type := es_monad exn iheap.
Definition irmonad : Type -> Type := es_monad irequest iheap.

Definition ixmonad_to_irmonad {A} : ixmonad A -> irmonad A :=
  with_except IRRaise.

Definition irmonad_to_ixmonad {A} : irmonad A -> ixmonad A :=
  with_except irequest_to_exn.

Definition except_exn_to_ixmonad {A} : except.t exn A -> ixmonad A :=
  except_to_es_monad.

Definition except_exn_to_irmonad {A} (m : except.t exn A) : irmonad A :=
  except_to_es_monad (except.with_except IRRaise m).
