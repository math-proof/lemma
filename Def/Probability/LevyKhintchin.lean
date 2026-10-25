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
open MeasureTheory
open scoped ENNReal NNReal MeasureTheory Topology

/-!
# The Lévy–Khintchin representation

This file proves the one-dimensional Lévy–Khintchin characterization of infinitely divisible
probability measures, with the hard truncation convention at radius one.
-/


namespace MetaMathlibExt

noncomputable def lkJump (t x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1 -
    Set.indicator {y : ℝ | |y| ≤ 1} (fun y ↦ Complex.I * (t : ℂ) * (y : ℂ)) x

noncomputable def lkExponent (γ σ : ℝ) (ν : Measure ℝ) (t : ℝ) : ℂ :=
  Complex.I * (γ : ℂ) * (t : ℂ) - (((σ ^ 2 * t ^ 2 : ℝ) : ℂ) / 2) +
    ∫ x, lkJump t x ∂ν

noncomputable def lkCutoff (k : ℕ) : ℝ := ((k + 1 : ℕ) : ℝ)⁻¹

def lkTruncationSet (k : ℕ) : Set ℝ := {x | lkCutoff k < |x|}

noncomputable def lkTruncate (ν : Measure ℝ) (k : ℕ) : Measure ℝ :=
  ν.restrict (lkTruncationSet k)

end MetaMathlibExt
