import Mathlib.Analysis.Real.Sqrt
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (hx : x ∈ Set.Ioc (-1) 0)
  (hy : y ∈ Set.Ioc (-1) 0)
  (hxy : x < y) :
-- imply
  y * Real.sqrt (1 - x ^ 2) > x * Real.sqrt (1 - y ^ 2) := by
-- proof
  obtain ⟨hx1, hx0⟩ := Set.mem_Ioc.mp hx
  obtain ⟨hy1, hy0⟩ := Set.mem_Ioc.mp hy
  have h1x : 0 ≤ 1 - x ^ 2 := by nlinarith
  have h1y : 0 ≤ 1 - y ^ 2 := by nlinarith
  set a := y * Real.sqrt (1 - x ^ 2) with ha_def
  set b := x * Real.sqrt (1 - y ^ 2) with hb_def
  have ha0 : a ≤ 0 := by
    rw [ha_def]
    exact mul_nonpos_of_nonpos_of_nonneg hy0 (Real.sqrt_nonneg _)
  have hb0 : b < 0 := by
    rw [hb_def]
    exact mul_neg_of_neg_of_pos (by linarith) (Real.sqrt_pos.mpr (by nlinarith))
  have hsq : a ^ 2 < b ^ 2 := by
    rw [ha_def, hb_def, mul_pow, Real.sq_sqrt h1x, mul_pow, Real.sq_sqrt h1y]
    nlinarith
  nlinarith [sq_nonneg (a - b)]


-- created on 2020-11-28
