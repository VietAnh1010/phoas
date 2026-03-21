From Stdlib Require Import Arith.
From shift_reset.lib Require Import signatures signature_laws.
From shift_reset.monad Require Import writer transformers.
From proofs.monad Require Import writer.

Compute (fun R W A => cont_t R (writer_t W identity) A).
Compute (fun W R A => writer_t W (cont_t R identity) A).

Module NatMonoid <: Monoid.
  Definition t := nat.
  Definition empty := O.
  Definition append := Nat.add.
End NatMonoid.

Module NatMonoidLaws <: MonoidLaws NatMonoid.
  Definition append_assoc : forall x y z, x + y + z = x + (y + z).
  Proof. symmetry. apply Nat.add_assoc. Qed.
  Definition append_empty_l := Nat.add_0_l.
  Definition append_empty_r := Nat.add_0_r.
End NatMonoidLaws.

Module WriterNat := Make NatMonoid.
Module WriterNatLaws := MakeLaws NatMonoid NatMonoidLaws WriterNat.
Print WriterNatLaws.
