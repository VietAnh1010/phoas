From shift_reset.monad Require Import cont except state.
From shift_reset.monad Require Import ce_monad cs_monad.
From shift_reset.monad Require Import ec_monad es_monad.
From shift_reset.monad Require Import sc_monad se_monad.
From shift_reset.monad Require Import ces_monad esc_monad.

Definition except_to_es_monad {E S A} (m : except.except E A) : es_monad E S A :=
  ESMonad (fun s => (run_except m, s)).

Definition state_to_es_monad {E S A} (m : state.state S A) : es_monad E S A :=
  ESMonad (fun s => let (x, s) := run_state m s in (inr x, s)).

Definition except_to_se_monad {S E A} (m : except.except E A) : se_monad S E A :=
  SEMonad
    (fun s =>
       match run_except m with
       | inl e => inl e
       | inr x => inr (x, s)
       end).

Definition state_to_se_monad {S E A} (m : state.state S A) : se_monad S E A :=
  SEMonad (fun s => inr (run_state m s)).

Definition except_to_ec_monad {E R A} (m : except.except E A) : ec_monad E R A :=
  ECMonad
    (fun h k =>
       match run_except m with
       | inl e => h e
       | inr x => k x
       end).

Definition cont_to_ec_monad {E R A} (m : cont.cont R A) : ec_monad E R A :=
  ECMonad (fun _ => run_cont m).

Definition state_to_sc_monad {S R A} (m : state.state S A) : sc_monad S R A :=
  SCMonad (fun s k => let (x, s) := run_state m s in k x s).

Definition cont_to_sc_monad {S R A} (m : cont.cont R A) : sc_monad S R A :=
  SCMonad (fun s k => run_cont m (fun x => k x s)).

Definition except_to_esc_monad {E S R A} (m : except.except E A) : esc_monad E S R A :=
  ESCMonad
    (fun s h k =>
       match run_except m with
       | inl e => h e s
       | inr x => k x s
       end).

Definition state_to_esc_monad {E S R A} (m : state.state S A) : esc_monad E S R A :=
  ESCMonad (fun s _ k => let (x, s) := run_state m s in k x s).

Definition cont_to_esc_monad {E S R A} (m : cont.cont R A) : esc_monad E S R A :=
  ESCMonad (fun s _ k => run_cont m (fun x => k x s)).

Definition except_to_ces_monad {R E S A} (m : except.except E A) : ces_monad R E S A :=
  CESMonad
    (fun k s =>
       match run_except m with
       | inl e => (inl e, s)
       | inr x => k x s
       end).

Definition state_to_ces_monad {R E S A} (m : state.state S A) : ces_monad R E S A :=
  CESMonad (fun k s => let (x, s) := run_state m s in k x s).

Definition es_monad_to_esc_monad {E S R A} (m : es_monad E S A) : esc_monad E S R A :=
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
