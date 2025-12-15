From shift_reset.monad Require Import except state ec_monad es_monad ces_monad esc_monad.

Definition except_to_es_monad {E S A} (m : except.except E A) : es_monad E S A :=
  ESMonad (fun s => (run_except m, s)).

Definition state_to_es_monad {E S A} (m : state.state S A) : es_monad E S A :=
  ESMonad (fun s => let (x, s) := run_state m s in (inr x, s)).

Definition except_to_ec_monad {E R A} (m : except.except E A) : ec_monad E R A :=
  ECMonad
    (fun h k =>
       match run_except m with
       | inl e => h e
       | inr x => k x
       end).

Definition except_to_esc_monad {E R S A} (m : except.except E A) : esc_monad E S R A :=
  ESCMonad
    (fun s h k =>
       match run_except m with
       | inl e => h e s
       | inr x => k x s
       end).

Definition es_monad_to_esc_monad {E R S A} (m : es_monad E S A) : esc_monad E S R A :=
  ESCMonad
    (fun s h k =>
       let (m, s) := run_es_monad m s in
       match m with
       | inl e => h e s
       | inr x => k x s
       end).

Definition es_monad_to_ces_monad {R E S A} (m : es_monad E S A) : ces_monad R E S A :=
  CESMonad
    (fun k s =>
       let (m, s) := run_es_monad m s in
       match m with
       | inl e => (inl e, s)
       | inr x => k x s
       end).
