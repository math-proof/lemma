/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionSmooth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Abbrev.v1.Atlas.DifferentialAnalysis.code.ConvolutionSmooth
open scoped ZeroAtInfty Convolution SchwartzMap ContDiff
open MeasureTheory Filter Topology Function Set TestFunctions
open ContinuousLinearMap


noncomputable section

namespace ConvolutionSmooth

/-- The convolution `v ⋆ ψ` of a `C₀` function `v` (continuous, vanishing at infinity)
with a Schwartz function `ψ`, as a function on Euclidean space. -/
def c0ConvSchwartz {n : ℕ} (v : C₀(EuclideanSpace ℝ (Fin n), ℂ))
    (ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) : EuclideanSpace ℝ (Fin n) → ℂ :=
  (v : EuclideanSpace ℝ (Fin n) → ℂ) ⋆[mulBilin] (ψ : EuclideanSpace ℝ (Fin n) → ℂ)


end ConvolutionSmooth
end
