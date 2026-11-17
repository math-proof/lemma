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
open scoped ZeroAtInfty
open Filter Topology


public noncomputable section

namespace TestFunctions

variable (n : ℕ)

/-- A continuous, complex-valued function on `ℝⁿ` that vanishes at infinity, is `C¹`,
and whose first-order partial derivatives also vanish at infinity. -/
structure ContDiffZeroAtInfty extends
    C₀(EuclideanSpace ℝ (Fin n), ℂ) where
  contDiff_one : ContDiff ℝ 1 ⇑toZeroAtInftyContinuousMap
  partialDeriv_zero_at_infty (j : Fin n) :
    Tendsto
      (fun x : EuclideanSpace ℝ (Fin n) =>
        fderiv ℝ (⇑toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1))
      (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0)

end TestFunctions
end
