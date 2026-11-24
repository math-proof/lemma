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
public import Theorem.Probability.LevyKhintchin.Part12
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

noncomputable def lkTaylorRemainder (t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ) * z) - 1 - Complex.I * (t : ℂ) * z

noncomputable def lkSecondSlope (t : ℝ) : ℂ → ℂ :=
  (Function.swap dslope (0 : ℂ))^[2] (lkTaylorRemainder t)

end MetaMathlibExt
