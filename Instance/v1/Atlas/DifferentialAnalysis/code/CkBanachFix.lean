/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanachFix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.DifferentialAnalysis.code.CkBanach.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.CkBanach
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Theorem.v1.Atlas.DifferentialAnalysis.code.CkBanachFix
open scoped ZeroAtInfty
open Filter Topology Finset


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
