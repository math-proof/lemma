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
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.SpecialFunctions.Part1Ch9Entry24Dougall.Part6
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry24Dougall

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem norm_le_one_of_mem_closedLens {z : ℂ} (hz : z ∈ closedLens) :
    ‖z‖ ≤ 1 := by
  have h0 : z ∈ Metric.closedBall (0 : ℂ) 1 := hz.1
  have hdist : dist z (0 : ℂ) ≤ 1 := Metric.mem_closedBall.mp h0
  rwa [dist_eq_norm, sub_zero] at hdist

theorem norm_one_sub_le_one_of_mem_closedLens {z : ℂ}
    (hz : z ∈ closedLens) : ‖(1 : ℂ) - z‖ ≤ 1 := by
  have h1 : z ∈ Metric.closedBall (1 : ℂ) 1 := hz.2
  have hdist : dist z (1 : ℂ) ≤ 1 := Metric.mem_closedBall.mp h1
  rw [dist_eq_norm] at hdist
  have hrev : ‖(1 : ℂ) - z‖ = ‖z - 1‖ := norm_sub_rev _ _
  rwa [hrev]

theorem re_pos_of_mem_closedLens {w : ℂ}
    (hw1 : ‖(1 : ℂ) - w‖ ≤ 1) (hwne : w ≠ 0) : 0 < w.re := by
  by_contra hneg
  push Not at hneg
  have hle : w.re ≤ 0 := hneg
  have hsq : ‖(1 : ℂ) - w‖ ^ 2
      = (1 - w.re) * (1 - w.re) + w.im * w.im := by
    have hdef : ‖(1 : ℂ) - w‖ ^ 2
        = ((1 - w).re) * ((1 - w).re) + ((1 - w).im) * ((1 - w).im) :=
      RCLike.norm_sq_eq_def
    have hre : ((1 : ℂ) - w).re = 1 - w.re := by simp
    have him : ((1 : ℂ) - w).im = -w.im := by simp
    rw [hre, him] at hdef
    have hnegmul : (-w.im) * (-w.im) = w.im * w.im := by ring
    rw [hnegmul] at hdef
    exact hdef
  have hsq_le : ‖(1 : ℂ) - w‖ ^ 2 ≤ 1 := by
    have hnn : (0 : ℝ) ≤ ‖(1 : ℂ) - w‖ := norm_nonneg _
    calc ‖(1 : ℂ) - w‖ ^ 2 ≤ 1 ^ 2 :=
          pow_le_pow_left₀ hnn hw1 2
      _ = 1 := one_pow _
  have hsum_le : (1 - w.re) * (1 - w.re) + w.im * w.im ≤ 1 := by
    rw [← hsq]
    exact hsq_le
  have h1a : (1 : ℝ) ≤ 1 - w.re := by linarith
  have hsq1 : (1 : ℝ) ≤ (1 - w.re) * (1 - w.re) := by
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ (1 - w.re) * (1 - w.re) :=
          mul_le_mul h1a h1a (by norm_num) (by linarith)
  have hbb : (0 : ℝ) ≤ w.im * w.im := mul_self_nonneg _
  have hXeq : (1 - w.re) * (1 - w.re) = 1 := by
    have hXle : (1 - w.re) * (1 - w.re) ≤ 1 := by linarith
    exact le_antisymm hXle hsq1
  have hYeq : w.im * w.im = 0 := by linarith
  have him0 : w.im = 0 := mul_self_eq_zero.mp hYeq
  have hre0 : w.re = 0 := by
    have haa : w.re * (w.re - 2) = 0 := by
      have hring : w.re * (w.re - 2)
          = (1 - w.re) * (1 - w.re) - 1 := by ring
      rw [hring, hXeq, sub_self]
    have hor := mul_eq_zero.mp haa
    rcases hor with h0 | h2
    · exact h0
    · have h2eq : w.re = 2 := by linarith
      linarith
  have hw0 : w = 0 := by
    rw [Complex.ext_iff]
    simp [hre0, him0]
  exact hwne hw0

theorem mem_slitPlane_of_mem_closedLens {z : ℂ} (hz : z ∈ closedLens)
    (hne : z ≠ 0) : z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl (re_pos_of_mem_closedLens
    (norm_one_sub_le_one_of_mem_closedLens hz) hne)

theorem one_sub_mem_slitPlane_of_mem_closedLens {z : ℂ}
    (hz : z ∈ closedLens) (hne : (1 : ℂ) - z ≠ 0) :
    (1 : ℂ) - z ∈ Complex.slitPlane := by
  have hz0 : ‖z‖ ≤ 1 := norm_le_one_of_mem_closedLens hz
  have h1 : ‖(1 : ℂ) - ((1 : ℂ) - z)‖ ≤ 1 := by
    have heq : (1 : ℂ) - ((1 : ℂ) - z) = z := by ring
    rw [heq]
    exact hz0
  have hpos : 0 < ((1 : ℂ) - z).re :=
    re_pos_of_mem_closedLens h1 hne
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl hpos

end
end Entry24Dougall
end Ramanujan.Part1Ch9
end
