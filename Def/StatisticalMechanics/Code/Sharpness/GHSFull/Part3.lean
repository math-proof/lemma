/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.GHSFull.Part2
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000


namespace StatMech

namespace Sharpness

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def flipEquiv : ConfigSpace V ≃ ConfigSpace V where
  toFun := flipCfg
  invFun := flipCfg
  left_inv := by intro s; funext x; unfold flipCfg; cases s x <;> rfl
  right_inv := by intro s; funext x; unfold flipCfg; cases s x <;> rfl


end Sharpness
end StatMech
