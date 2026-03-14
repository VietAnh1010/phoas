From shift_reset.monad Require Import cont except select state
  ce_monad cs_monad ec_monad es_monad sc_monad se_monad
  ces_monad esc_monad.

Definition except_to_es_monad {E S A} (m : except.t E A) : es_monad E S A :=
  ESMonad (fun s => (run_except m, s)).

Definition state_to_es_monad {E S A} (m : state.t S A) : es_monad E S A :=
  ESMonad (fun s => let (x, s) := run_state m s in (inr x, s)).

Definition except_to_se_monad {S E A} (m : except.t E A) : se_monad S E A :=
  SEMonad
    (fun s =>
       match run_except m with
       | inl e => inl e
       | inr x => inr (x, s)
       end).

Definition state_to_se_monad {S E A} (m : state.t S A) : se_monad S E A :=
  SEMonad (fun s => inr (run_state m s)).

Definition except_to_ec_monad {E R A} (m : except.t E A) : ec_monad E R A :=
  ECMonad
    (fun h k =>
       match run_except m with
       | inl e => h e
       | inr x => k x
       end).

Definition cont_to_ec_monad {E R A} (m : cont.t R A) : ec_monad E R A :=
  ECMonad (fun _ => run_cont m).

Definition state_to_sc_monad {S R A} (m : state.t S A) : sc_monad S R A :=
  SCMonad (fun s k => let (x, s) := run_state m s in k x s).

Definition cont_to_sc_monad {S R A} (m : cont.t R A) : sc_monad S R A :=
  SCMonad (fun s k => run_cont m (fun x => k x s)).

Definition except_to_esc_monad {E S R A} (m : except.t E A) : esc_monad E S R A :=
  ESCMonad
    (fun s h k =>
       match run_except m with
       | inl e => h e s
       | inr x => k x s
       end).

Definition state_to_esc_monad {E S R A} (m : state.t S A) : esc_monad E S R A :=
  ESCMonad (fun s _ k => let (x, s) := run_state m s in k x s).

Definition cont_to_esc_monad {E S R A} (m : cont.t R A) : esc_monad E S R A :=
  ESCMonad (fun s _ k => run_cont m (fun x => k x s)).

Definition except_to_ces_monad {R E S A} (m : except.t E A) : ces_monad R E S A :=
  CESMonad
    (fun k s =>
       match run_except m with
       | inl e => (inl e, s)
       | inr x => k x s
       end).

Definition state_to_ces_monad {R E S A} (m : state.t S A) : ces_monad R E S A :=
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

Definition select_to_cont {R A} (m : select.t R A) : cont.t R A :=
  Cont (fun k => k (run_select m k)).
