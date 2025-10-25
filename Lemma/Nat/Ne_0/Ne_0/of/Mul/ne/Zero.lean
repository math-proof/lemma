import Lemma.Algebra.Ne_0.of.Mul.ne.Zero
open Algebra


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


-- created on 2025-04-12
