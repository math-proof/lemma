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
import Structure.v1.Atlas.DifferentialAnalysis.code.TestFunctions
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

/-- Pullback of continuous linear functionals along a continuous linear map
`ι : V →L[𝕜] U`: sends a dual element on `U` to its restriction along `ι`. -/
def restrictDual (ι : V →L[𝕜] U) : (U →L[𝕜] 𝕜) →L[𝕜] (V →L[𝕜] 𝕜) :=
  (compL 𝕜 V U 𝕜).flip ι

/-- The `C^k` sup-norm of a function `f : ℝⁿ → ℂ`: sum of sup norms of all partial
derivatives up to order `k`. -/
def ckNorm (n : ℕ) : ℕ → (EuclideanSpace ℝ (Fin n) → ℂ) → ℝ
  | 0, f => ⨆ x, ‖f x‖
  | k + 1, f =>
    ckNorm n k f +
      Finset.sum Finset.univ fun j : Fin n =>
        ckNorm n k fun x => fderiv ℝ f x (EuclideanSpace.single j 1)

end RestrictionOfFunctionals
end TestFunctions
end
