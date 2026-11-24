module
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Topology.UrysohnsLemma
public import Def.v1.Atlas.DifferentialAnalysis.code.JordanDecomposition.Part5
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.JordanDecomposition
public import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras
public import Def.v1.Atlas.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/RieszRepresentation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
section PositiveCase

end PositiveCase

noncomputable section

open MeasureTheory Set TopologicalSpace CompactlySupported
  CompactlySupportedContinuousMap

open scoped ZeroAtInfty ENNReal BoundedContinuousFunction

namespace RieszRepresentation

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- Restrict a positive continuous linear functional on `C₀(X, ℝ)` to the subspace of compactly
supported continuous functions, producing a positive linear functional on `C_c(X, ℝ)`. -/
def restrictPositiveCLFToCc
    {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (u : ZeroAtInftyContinuousMap X ℝ →L[ℝ] ℝ)
    (hu : ContinuousFunctions.IsPositiveFunctional u) :
    C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  MeasuresAndSigmaAlgebras.restrictC0ToCc u.toLinearMap (fun f hf => hu f hf)

end RieszRepresentation
end
