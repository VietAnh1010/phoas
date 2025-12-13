From shift_reset.monad Require except state es_monad.

Definition except_to_es_monad {E S A} (m : except.except E A) : es_monad.es_monad E S A :=
  es_monad.ESMonad (fun s => (except.run_except m, s)).

Definition state_to_es_monad {E S A} (m : state.state S A) : es_monad.es_monad E S A :=
  es_monad.ESMonad (fun s => let (x, s) := state.run_state m s in (inr x, s)).
