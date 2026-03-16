From shift_reset.lib Require Import monad_transformer.

Compute (fun R W A => cont_t R (writer_t W identity) A).
Compute (fun W R A => writer_t W (cont_t R identity) A).
