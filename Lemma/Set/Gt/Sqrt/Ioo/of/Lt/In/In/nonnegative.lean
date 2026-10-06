import Mathlib.Analysis.Real.Sqrt
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (hx : x ∈ Set.Ico 0 1)
  (hy : y ∈ Set.Ico 0 1)
  (hxy : x < y) :
-- imply
  y * Real.sqrt (1 - x ^ 2) > x * Real.sqrt (1 - y ^ 2) := by
-- proof
  obtain ⟨hx0, hx1⟩ := Set.mem_Ico.mp hx
  obtain ⟨hy0, hy1⟩ := Set.mem_Ico.mp hy
  have h1x : 0 ≤ 1 - x ^ 2 := by nlinarith
  have h1y : 0 ≤ 1 - y ^ 2 := by nlinarith
  have hypos : 0 < y := by linarith
  set a := y * Real.sqrt (1 - x ^ 2) with ha_def
  set b := x * Real.sqrt (1 - y ^ 2) with hb_def
  have ha0 : 0 < a := by
    rw [ha_def]
    exact mul_pos hypos (Real.sqrt_pos.mpr (by nlinarith))
  have hb0 : 0 ≤ b := by
    rw [hb_def]
    exact mul_nonneg hx0 (Real.sqrt_nonneg _)
  have hsq : a ^ 2 > b ^ 2 := by
    rw [ha_def, hb_def, mul_pow, Real.sq_sqrt h1x, mul_pow, Real.sq_sqrt h1y]
    nlinarith
  nlinarith [sq_nonneg (a - b)]


-- created on 2020-11-28
