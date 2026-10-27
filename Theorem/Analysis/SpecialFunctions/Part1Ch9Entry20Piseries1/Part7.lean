/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.SpecialFunctions.Part1Ch9Entry20Piseries1.Part7
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry20Piseries1

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem auxAr_summable {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    Summable (auxAr_term r x) := by
  have habs : |r| < 1 := by rwa [abs_of_nonneg hr0]
  have hgeo : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_abs_lt_one habs
  have hshift : Summable (fun j : ℕ => r ^ (j + 1)) :=
    (summable_nat_add_iff 1).mpr hgeo
  apply Summable.of_norm_bounded hshift
  intro j
  have hsin : |Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x)| ≤ 1 :=
    Real.abs_sin_le_one _
  have hpos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
    apply pow_pos
    exact Nat.cast_pos.mpr (Nat.succ_pos j)
  have hle1 : (1 : ℝ) ≤ ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
    have h1 : (1 : ℝ) ≤ ((((j + 1 : ℕ)) : ℝ)) := by
      have h : (1 : ℕ) ≤ j + 1 := Nat.succ_le_succ (Nat.zero_le j)
      exact_mod_cast h
    calc (1 : ℝ) = 1 ^ 2 := (one_pow 2).symm
      _ ≤ ((((j + 1 : ℕ)) : ℝ) ^ 2) := pow_le_pow_left₀ zero_le_one h1 2
  have hdiv : (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2) ≤ 1 := (div_le_one hpos).mpr hle1
  have hnn_pow : (0 : ℝ) ≤ r ^ (j + 1) := pow_nonneg hr0 _
  unfold auxAr_term
  rw [Real.norm_eq_abs, abs_div, abs_mul]
  have habs2 : |((((j + 1 : ℕ)) : ℝ) ^ 2)| = ((((j + 1 : ℕ)) : ℝ) ^ 2) :=
    abs_of_pos hpos
  rw [habs2]
  have hr_abs : |r ^ (j + 1)| = r ^ (j + 1) := abs_of_nonneg hnn_pow
  rw [hr_abs]
  calc r ^ (j + 1) * |Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x)| /
        ((((j + 1 : ℕ)) : ℝ) ^ 2)
      = (r ^ (j + 1) * |Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x)|) *
        (1 / ((((j + 1 : ℕ)) : ℝ) ^ 2)) := by ring
    _ ≤ (r ^ (j + 1) * 1) * 1 := by
        apply mul_le_mul _ hdiv (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hsin hnn_pow
    _ = r ^ (j + 1) := by ring

theorem auxAr_hasDerivAt {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    HasDerivAt (auxAr r) (∑' j : ℕ, auxAr_deriv_term r x j) x := by
  have habs : |r| < 1 := by rwa [abs_of_nonneg hr0]
  have hgeo : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_abs_lt_one habs
  have hshift : Summable (fun j : ℕ => r ^ (j + 1)) :=
    (summable_nat_add_iff 1).mpr hgeo
  have hu : Summable (fun j : ℕ => 2 * r ^ (j + 1)) := hshift.mul_left 2
  have hterm : ∀ j : ℕ, ∀ y : ℝ,
      HasDerivAt (fun y => auxAr_term r y j) (auxAr_deriv_term r y j) y := by
    intro j y
    unfold auxAr_term auxAr_deriv_term
    have hkne : ((((j + 1 : ℕ)) : ℝ)) ≠ 0 := by
      apply Nat.cast_ne_zero.mpr
      omega
    have hlin : HasDerivAt (fun y : ℝ => 2 * ((((j + 1 : ℕ)) : ℝ)) * y)
        (2 * ((((j + 1 : ℕ)) : ℝ))) y := by
      have h := (hasDerivAt_id y).const_mul (2 * ((((j + 1 : ℕ)) : ℝ)))
      simpa using h
    have hsin := hlin.sin
    have hmul := hsin.const_mul (r ^ (j + 1) / ((((j + 1 : ℕ)) : ℝ) ^ 2))
    have heq_fun : (fun y => r ^ (j + 1) / ((((j + 1 : ℕ)) : ℝ) ^ 2) *
        Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y)) =
        (fun y => r ^ (j + 1) * Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y) /
          ((((j + 1 : ℕ)) : ℝ) ^ 2)) := by
      funext y
      ring
    rw [heq_fun] at hmul
    have heq_deriv : (r ^ (j + 1) / ((((j + 1 : ℕ)) : ℝ) ^ 2)) *
        (Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * y) * (2 * ((((j + 1 : ℕ)) : ℝ)))) =
        2 * r ^ (j + 1) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * y) /
          ((((j + 1 : ℕ)) : ℝ)) := by
      field_simp
    rw [heq_deriv] at hmul
    exact hmul
  have hbound : ∀ j : ℕ, ∀ y : ℝ,
      ‖auxAr_deriv_term r y j‖ ≤ 2 * r ^ (j + 1) := by
    intro j y
    have hcos : |Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * y)| ≤ 1 :=
      Real.abs_cos_le_one _
    have hpos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ)) :=
      Nat.cast_pos.mpr (Nat.succ_pos j)
    have hle1 : (1 : ℝ) ≤ ((((j + 1 : ℕ)) : ℝ)) := by
      have h : (1 : ℕ) ≤ j + 1 := Nat.succ_le_succ (Nat.zero_le j)
      exact_mod_cast h
    have hdiv : (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ)) ≤ 1 := (div_le_one hpos).mpr hle1
    have hnn : (0 : ℝ) ≤ 2 * r ^ (j + 1) := by positivity
    unfold auxAr_deriv_term
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul]
    have habs2 : |((((j + 1 : ℕ)) : ℝ))| = ((((j + 1 : ℕ)) : ℝ)) := abs_of_pos hpos
    rw [habs2]
    have hr_abs : |r ^ (j + 1)| = r ^ (j + 1) := abs_of_nonneg (pow_nonneg hr0 _)
    rw [hr_abs, show |(2 : ℝ)| = 2 from abs_of_pos (by norm_num)]
    calc 2 * r ^ (j + 1) * |Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * y)| /
          ((((j + 1 : ℕ)) : ℝ))
        = (2 * r ^ (j + 1) * |Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * y)|) *
          (1 / ((((j + 1 : ℕ)) : ℝ))) := by ring
      _ ≤ (2 * r ^ (j + 1) * 1) * 1 := by
          apply mul_le_mul _ hdiv (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hcos (by positivity)
      _ = 2 * r ^ (j + 1) := by ring
  have hmain := hasDerivAt_tsum hu hterm hbound (auxAr_summable hr0 hr1 x) x
  have efun : (fun z => ∑' j : ℕ, auxAr_term r z j) = auxAr r := by
    funext z
    rfl
  rw [efun] at hmain
  exact hmain

end
end Entry20Piseries1
end Ramanujan.Part1Ch9
end
