/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/RieszRepresentation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.LevyConvergence

import Mathlib.Topology.UrysohnsLemma
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.JordanDecomposition
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.JordanDecomposition
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras

noncomputable section

open MeasureTheory Set TopologicalSpace CompactlySupported
  CompactlySupportedContinuousMap
open scoped ZeroAtInfty ENNReal BoundedContinuousFunction

namespace RieszRepresentation

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

section PositiveCase

end PositiveCase

/-- Restrict a positive continuous linear functional on `C₀(X, ℝ)` to the subspace of compactly
supported continuous functions, producing a positive linear functional on `C_c(X, ℝ)`. -/
def restrictPositiveCLFToCc
    {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (u : ZeroAtInftyContinuousMap X ℝ →L[ℝ] ℝ)
    (hu : ContinuousFunctions.IsPositiveFunctional u) :
    C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  MeasuresAndSigmaAlgebras.restrictC0ToCc u.toLinearMap (fun f hf => hu f hf)
