/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Def.Probability.LevyKhintchin
open MeasureTheory
open scoped ENNReal NNReal MeasureTheory Topology

/-!
# The Lévy–Khintchin representation

This file proves the one-dimensional Lévy–Khintchin characterization of infinitely divisible
probability measures, with the hard truncation convention at radius one.
-/


namespace MetaMathlibExt

lemma lkCutoff_pos (k : ℕ) : 0 < lkCutoff k := by
  simp only [lkCutoff]
  positivity

lemma lkCutoff_le_one (k : ℕ) : lkCutoff k ≤ 1 := by
  simp only [lkCutoff]
  apply (inv_le_one₀ (by positivity)).2
  norm_num

lemma lk_cutoff_sq_le_moment {k : ℕ} {x : ℝ} (hx : x ∈ lkTruncationSet k) :
    lkCutoff k ^ 2 ≤ min 1 (x ^ 2) := by
  apply le_min
  · simpa using (sq_le_sq₀ (lkCutoff_pos k).le zero_le_one).2 (lkCutoff_le_one k)
  · rw [← sq_abs x]
    exact (sq_le_sq₀ (lkCutoff_pos k).le (abs_nonneg x)).2 hx.le

lemma lk_restrict_away_zero_finite {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (k : ℕ) :
    IsFiniteMeasure (lkTruncate ν k) := by
  apply IsFiniteMeasure.mk
  let ε : ℝ≥0∞ := ENNReal.ofReal (lkCutoff k ^ 2)
  have hε : ε ≠ 0 := by
    dsimp only [ε]
    exact ne_of_gt (ENNReal.ofReal_pos.2 (sq_pos_of_pos (lkCutoff_pos k)))
  have h_meas : AEMeasurable (fun x : ℝ ↦ ENNReal.ofReal (min 1 (x ^ 2))) ν := by
    have h_cont : Continuous (fun x : ℝ ↦ min 1 (x ^ 2)) := by fun_prop
    exact h_cont.measurable.aemeasurable.ennreal_ofReal
  calc
    lkTruncate ν k Set.univ = ν (lkTruncationSet k) := by
      rw [lkTruncate, Measure.restrict_apply MeasurableSet.univ]
      simp
    _ ≤ ν {x | ε ≤ ENNReal.ofReal (min 1 (x ^ 2))} := by
      apply measure_mono
      intro x hx
      exact ENNReal.ofReal_le_ofReal (lk_cutoff_sq_le_moment hx)
    _ ≤ (∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν) / ε :=
      meas_ge_le_lintegral_div h_meas hε ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.div_lt_top (ne_of_lt hν) hε

end MetaMathlibExt
