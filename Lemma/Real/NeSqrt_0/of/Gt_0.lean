import Lemma.Nat.EqSquare_0.of.Eq_0
import Lemma.Real.EqSquareSqrt.of.Gt_0
import Lemma.Algebra.NotGt.of.Eq
open Algebra Real Nat


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x > 0) :
-- imply
  √x ≠ 0 := by
-- proof
  -- Assume for contradiction that √x = 0
  intro h₀
  have h_Eq_0 := EqSquare_0.of.Eq_0 h₀
  have := EqSquareSqrt.of.Gt_0 h
  rw [this] at h_Eq_0
  have := NotGt.of.Eq h_Eq_0
  contradiction


-- created on 2025-04-06
