import Lemma.Algebra.Mul.ne.Zero.of.Ne_0.Ne_0
import Lemma.Nat.Ne.of.Lt
open Algebra Nat


@[main]
private lemma main
  [Mul α]
  [Zero α]
  [NoZeroDivisors α]
  [Preorder α]
  {a b : α}
-- given
  (h₀ : a < 0)
  (h₁ : b < 0) :
-- imply
  a * b ≠ 0 := by
-- proof
  apply Mul.ne.Zero.of.Ne_0.Ne_0 <;>
  ·
    apply Ne.of.Lt
    assumption


-- created on 2025-07-12
