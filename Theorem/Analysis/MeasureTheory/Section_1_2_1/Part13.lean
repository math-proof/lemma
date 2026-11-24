module
public import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
public import Theorem.Analysis.Misc.RealERealENNReal
public import Theorem.Analysis.Misc.Combinatorics
public import Def.Analysis.MeasureTheory.Section_1_2_1.Part11
open BoundedInterval


public section

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/
lemma DyadicCube.isCube {d:ℕ} (n:ℤ) (a: Fin d → ℤ) : IsCube (DyadicCube n a) := by
  -- All sides have length 1/2^n
  use |2^(-n : ℤ)|
  intro i
  simp only [DyadicCube, BoundedInterval.length, BoundedInterval.b, BoundedInterval.a]
  -- Show ((a i + 1)/2^n - a i/2^n) = 1/2^n
  have h : (↑(a i) + 1) / (2:ℝ) ^ n - ↑(a i) / (2:ℝ) ^ n = (2:ℝ) ^ (-n) := by
    simp only [zpow_neg, ← sub_div]; norm_cast; simp [add_sub_cancel_left]
  rw [h]
  simp only [max_eq_left (zpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-n))]
  exact (abs_of_nonneg (zpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-n))).symm

