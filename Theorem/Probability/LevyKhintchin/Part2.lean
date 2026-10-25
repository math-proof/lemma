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
import Def.Probability.LevyKhintchin.Part2
open MeasureTheory
open scoped ENNReal NNReal MeasureTheory Topology

/-!
# The Lévy–Khintchin representation

This file proves the one-dimensional Lévy–Khintchin characterization of infinitely divisible
probability measures, with the hard truncation convention at radius one.
-/


namespace MetaMathlibExt

lemma lkConvPow_finite (ρ : Measure ℝ) [IsFiniteMeasure ρ] (n : ℕ) :
    IsFiniteMeasure (lkConvPow ρ n) := by
  induction n with
  | zero =>
      rw [lkConvPow]
      infer_instance
  | succ n ih =>
      rw [lkConvPow]
      infer_instance

lemma lk_charFun_convPow (ρ : Measure ℝ) [IsFiniteMeasure ρ] (n : ℕ) (t : ℝ) :
    charFun (lkConvPow ρ n) t = charFun ρ t ^ n := by
  induction n with
  | zero => simp [lkConvPow, charFun_dirac]
  | succ n ih =>
      rw [lkConvPow]
      let _ := lkConvPow_finite ρ n
      rw [charFun_conv, ih, pow_succ']

lemma lk_conv_apply_univ (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    (μ ∗ ν) Set.univ = μ Set.univ * ν Set.univ := by
  rw [Measure.conv, Measure.map_apply_of_aemeasurable (by fun_prop) MeasurableSet.univ]
  simp only [Set.preimage_univ]
  rw [Measure.prod_apply MeasurableSet.univ]
  simp [mul_comm]

lemma lkConvPow_apply_univ (ρ : Measure ℝ) [IsFiniteMeasure ρ] (n : ℕ) :
    lkConvPow ρ n Set.univ = ρ Set.univ ^ n := by
  induction n with
  | zero => simp [lkConvPow]
  | succ n ih =>
      rw [lkConvPow]
      let _ := lkConvPow_finite ρ n
      rw [lk_conv_apply_univ, ih, pow_succ']

end MetaMathlibExt
