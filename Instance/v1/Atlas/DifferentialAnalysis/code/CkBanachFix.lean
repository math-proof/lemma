module
public import Theorem.v1.Atlas.DifferentialAnalysis.code.CkBanach.Part2
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.CkBanach
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Theorem.v1.Atlas.DifferentialAnalysis.code.CkBanachFix
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

/-- The `NormedAddCommGroup` instance on `ContDiffZeroAtInfty n` via the `C^1₀` norm. -/
instance ContDiffZeroAtInfty.instNormedAddCommGroup :
    NormedAddCommGroup (ContDiffZeroAtInfty n) :=
  NormedAddCommGroup.ofCore ContDiffZeroAtInfty.normedSpaceCore

/-- The `ℂ`-`NormedSpace` instance on `ContDiffZeroAtInfty n`. -/
instance ContDiffZeroAtInfty.instNormedSpace :
    NormedSpace ℂ (ContDiffZeroAtInfty n) :=
  NormedSpace.ofCore ContDiffZeroAtInfty.normedSpaceCore

end TestFunctions
end
