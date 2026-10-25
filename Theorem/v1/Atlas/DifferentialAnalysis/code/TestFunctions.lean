/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TestFunctions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.DenseEmbedding
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Def.v1.Atlas.DifferentialAnalysis.code.TestFunctions.Part2
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

/-- The Japanese bracket `⟨x⟩` is strictly positive. -/
theorem japaneseBracket_pos (x : EuclideanSpace ℝ (Fin n)) :
    0 < japaneseBracket n x := by
  unfold japaneseBracket
  apply Real.sqrt_pos_of_pos
  positivity

end WeightedSpaces
end RestrictionOfFunctionals
end TestFunctions
end
