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
import Def.Analysis.Calculus.Borel.Part4
/-!
# Borel's theorem on arbitrary jets at a point (real line)
-/


namespace Real.Calculus.Borel

open scoped Topology ContDiff

lemma g_eq_scaled (a : ℕ → ℝ) (m : ℕ) :
    g a m = fun x => coeff a m * radius a m ^ m * poly m ((radius a m)⁻¹ * x) := by
  funext x
  have hr : radius a m ≠ 0 := (radius_pos a m).ne'
  simp only [g, poly, mul_pow]
  rw [show coeff a m * radius a m ^ m *
          ((radius a m)⁻¹ ^ m * x ^ m * bump ((radius a m)⁻¹ * x))
        = coeff a m * (radius a m ^ m * (radius a m)⁻¹ ^ m) *
            (x ^ m * bump ((radius a m)⁻¹ * x)) from by ring,
      ← mul_pow, mul_inv_cancel₀ hr, one_pow, mul_one]
  ring

lemma g_contDiff (a : ℕ → ℝ) (m : ℕ) : ContDiff ℝ ∞ (g a m) := by
  unfold g
  exact (contDiff_const.mul (contDiff_id.pow m)).mul
    (bump.contDiff.comp (contDiff_const.mul contDiff_id))

lemma g_hasCompactSupport (a : ℕ → ℝ) (m : ℕ) : HasCompactSupport (g a m) := by
  apply HasCompactSupport.intro (K := Metric.closedBall (0 : ℝ) (2 * radius a m))
    (isCompact_closedBall _ _)
  intro x hx
  have hr : 0 < radius a m := radius_pos a m
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
  have hb : bump ((radius a m)⁻¹ * x) = 0 := by
    apply bump.zero_of_le_dist
    rw [dist_zero_right, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hr]
    change (2 : ℝ) ≤ (radius a m)⁻¹ * |x|
    rw [le_inv_mul_iff₀ hr]
    linarith
  simp only [g, hb, mul_zero]

end Real.Calculus.Borel
