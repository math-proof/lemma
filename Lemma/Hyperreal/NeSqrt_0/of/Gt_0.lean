import Lemma.Nat.EqSquare_0.of.Eq_0
import Lemma.Nat.NotGt.of.Eq
import Lemma.Hyperreal.EqSquareSqrt.of.Gt_0
open Nat Hyperreal


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : x > 0) :
-- imply
  √x ≠ 0 := by
-- proof
  intro h₀
  have h_Eq_0 := EqSquare_0.of.Eq_0 h₀
  have := EqSquareSqrt.of.Gt_0 h
  rw [this] at h_Eq_0
  have := NotGt.of.Eq h_Eq_0
  contradiction


-- created on 2025-12-10
