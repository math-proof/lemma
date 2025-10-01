import Lemma.Algebra.EqDivS.of.Eq
import Lemma.Algebra.EqDivMul.of.Ne_0
open Algebra


@[main]
private lemma main
  [MonoidWithZero α]
  [Div α]
  [MulDivCancelClass α]
  {a b x : α}
-- given
  (h₀ : a * x = b)
  (h₁ : x ≠ 0) :
-- imply
  a = b / x := by
-- proof
  have h := EqDivS.of.Eq h₀ x
  rw [EqDivMul.of.Ne_0 h₁] at h
  assumption


-- created on 2025-10-01
