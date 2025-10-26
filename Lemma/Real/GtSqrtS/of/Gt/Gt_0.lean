import Lemma.Nat.Ge.of.NotLt
import Lemma.Real.EqSquareSqrt.of.Ge_0
import Lemma.Real.EqSqrt_0.of.Lt_0
import Lemma.Real.GtSqrt_0.of.Gt_0
open Nat Real


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x > y)
  (h₁ : x > 0) :
-- imply
  √x > √y := by
-- proof
  by_cases h : y < 0
  ·
    rw [EqSqrt_0.of.Lt_0 h]
    apply GtSqrt_0.of.Gt_0 h₁
  ·
    have h := Ge.of.NotLt h
    -- Use the fact that the square root function is increasing on the positive real numbers.
    apply Real.lt_sqrt_of_sq_lt
    rwa [EqSquareSqrt.of.Ge_0 h]


-- created on 2025-04-06
