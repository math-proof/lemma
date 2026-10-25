/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Compactness.DeltaGeneratedSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Def.Analysis.Calculus.Borel.Part3
/-!
# Borel's theorem on arbitrary jets at a point (real line)
-/


namespace Real.Calculus.Borel

open scoped Topology ContDiff

lemma radius_pos (a : ℕ → ℝ) (m : ℕ) : 0 < radius a m := by
  apply lt_min one_pos
  have h := polyBound_nonneg m
  have hden : 0 < |coeff a m| * polyBound m + 1 := by
    have : 0 ≤ |coeff a m| * polyBound m := mul_nonneg (abs_nonneg _) h
    linarith
  exact div_pos (pow_pos (by norm_num) m) hden

lemma radius_le_one (a : ℕ → ℝ) (m : ℕ) : radius a m ≤ 1 := min_le_left _ _

lemma radius_bound (a : ℕ → ℝ) (m : ℕ) :
    |coeff a m| * polyBound m * radius a m ≤ (1 / 2) ^ m := by
  have h := polyBound_nonneg m
  have hD : 0 ≤ |coeff a m| * polyBound m := mul_nonneg (abs_nonneg _) h
  have hden : 0 < |coeff a m| * polyBound m + 1 := by linarith
  have hr : radius a m ≤ (1 / 2) ^ m / (|coeff a m| * polyBound m + 1) := min_le_right _ _
  have hpow : 0 < (1 / 2 : ℝ) ^ m := pow_pos (by norm_num) m
  calc |coeff a m| * polyBound m * radius a m
      ≤ |coeff a m| * polyBound m * ((1 / 2) ^ m / (|coeff a m| * polyBound m + 1)) :=
        mul_le_mul_of_nonneg_left hr hD
    _ ≤ (1 / 2) ^ m := by
        rw [← mul_div_assoc, div_le_iff₀ hden]
        nlinarith [hpow]

end Real.Calculus.Borel
