module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.MeasureTheory.Measure.IntegralCharFun
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Def.Probability.LevyKhintchin.Part9
open MeasureTheory
open scoped ENNReal NNReal MeasureTheory Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
/-!
# The Lévy–Khintchin representation

This file proves the one-dimensional Lévy–Khintchin characterization of infinitely divisible
probability measures, with the hard truncation convention at radius one.
-/
namespace MetaMathlibExt

lemma lkCanonicalWeight_nonneg (x : ℝ) : 0 ≤ lkCanonicalWeight x := by
  unfold lkCanonicalWeight
  positivity

lemma lkCanonicalWeight_le_one (x : ℝ) : lkCanonicalWeight x ≤ 1 := by
  unfold lkCanonicalWeight
  apply (div_le_one (by positivity : 0 < 1 + x ^ 2)).2
  linarith

lemma lk_canonicalWeight_div_32_le_one_sub_sinc (x : ℝ) :
    lkCanonicalWeight x / 32 ≤ 1 - Real.sinc x := by
  by_cases hx : |x| ≤ 2
  · have hw : lkCanonicalWeight x ≤ x ^ 2 := by
      unfold lkCanonicalWeight
      apply (div_le_iff₀ (by positivity : 0 < 1 + x ^ 2)).2
      nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]
    calc
      lkCanonicalWeight x / 32 ≤ x ^ 2 / 32 := by gcongr
      _ ≤ 1 - Real.sinc x := lk_sq_div_32_le_one_sub_sinc_of_abs_le_two hx
  · have hx2 : 2 < |x| := lt_of_not_ge hx
    have hx0 : x ≠ 0 := fun h ↦ by norm_num [h] at hx2
    have hsinc : Real.sinc x ≤ (2 : ℝ)⁻¹ :=
      (Real.sinc_le_inv_abs hx0).trans (inv_anti₀ (by norm_num) hx2.le)
    have hw : lkCanonicalWeight x ≤ 1 := lkCanonicalWeight_le_one x
    calc
      lkCanonicalWeight x / 32 ≤ 1 / 32 := by gcongr
      _ ≤ 1 - Real.sinc x := by norm_num at hsinc ⊢; linarith

end MetaMathlibExt
