import sympy.core.power
import Lemma.Real.GeSqrt_0
import Lemma.Int.GeSquare_0
import Lemma.Algebra.Ge.of.Ge.Ge
import Lemma.Nat.Eq.of.Le.Ge
import Lemma.Int.Eq_0.of.LeSquare_0
import Lemma.Real.Le_Sqrt.is.LeSquare.of.Ge_0.Ge_0
open Algebra Nat Int Real


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x² ≤ y) :
-- imply
  x ≤ √y := by
-- proof
  -- We need to show that x ≤ √y given x² ≤ y. We consider two cases: x ≥ 0 and x < 0.
  obtain hx | hx := le_total 0 x
  ·
    -- For each case, we use the fact that the square root of a non-negative number is non-negative.
    obtain hy | hy := le_total 0 y
    ·
      apply Le_Sqrt.of.LeSquare.Ge_0.Ge_0
      repeat assumption
    ·
      -- Case 2: x ≥ 0 and y < 0
      -- This case is impossible because y < 0 contradicts x² ≤ y (since x² is always non-negative).
      have := GeSquare_0 (a := x)
      have := Ge.of.Ge.Ge h this
      have := Eq.of.Le.Ge hy this
      rw [this]
      rw [this] at h
      norm_num
      have := Eq_0.of.LeSquare_0 h
      linarith
  ·
    have := GeSqrt_0 (x := y)
    linarith


-- created on 2025-04-06
-- updated on 2025-08-02
