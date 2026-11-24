module
public import Theorem.v1.Atlas.DifferentialAnalysis.code.CkBanach.Part2
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.CkBanach
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
open scoped ZeroAtInfty
open Filter Topology Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanachFix.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

set_option maxRecDepth 4000

namespace TestFunctions

variable {n : ℕ}

/-- The `j`-th partial derivative of `u` as a `C₀` continuous function (vanishing at infinity). -/
def ContDiffZeroAtInfty.partialDerivC0 (u : ContDiffZeroAtInfty n) (j : Fin n) :
    C₀(EuclideanSpace ℝ (Fin n), ℂ) where
  toFun x := fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1)
  continuous_toFun := u.continuous_partialDeriv j
  zero_at_infty' := u.partialDeriv_zero_at_infty j

end TestFunctions
end
