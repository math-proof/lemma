/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TestFunctions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Structure.v1.Atlas.DifferentialAnalysis.code.TestFunctions.Part3

@[expose] public section

open scoped ZeroAtInfty
open Filter Topology


noncomputable section

namespace TestFunctions

variable (n : ℕ)

section RestrictionOfFunctionals

open ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

variable {U : Type*} [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]

variable {n}

section WeightedSpaces

variable (n : ℕ)

/-- Underlying function `⟨x⟩^{-l} v(x)` for a weighted `C^k` element with witness `v`. -/
def WeightedContDiffZeroAtInfty.toFun {k l : ℕ}
    (u : WeightedContDiffZeroAtInfty n k l) (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  (↑(japaneseBracket n x ^ l))⁻¹ * u.witnessV.toZeroAtInftyContinuousMap x

end WeightedSpaces
end RestrictionOfFunctionals
end TestFunctions
end
