import Lemma.Nat.Ne_0.of.Mul.ne.Zero
import torch.Tensor
open Nat


@[main]
private lemma main
  [MulZeroClass α]
  {a b : α}
-- given
  (h : a * b ≠ 0) :
-- imply
  a ≠ 0 ∧ b ≠ 0 := by
-- proof
  constructor
  ·
    apply Ne_0.of.Mul.ne.Zero.left h
  ·
    apply Ne_0.of.Mul.ne.Zero h


@[main]
private lemma tensor
  [MulZeroClass α]
  {a b : Tensor α [n]}
-- given
  (h : a * b ≠ 0) :
-- imply
  a ≠ 0 ∧ b ≠ 0 :=
-- proof
  main h


-- created on 2018-01-22
-- updated on 2026-09-27
