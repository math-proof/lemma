/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_dpairsmodular.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part8
open Finset


namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]


def rc_dkern (S T : Finset α) : ℕ := if Disjoint S T then 1 else 0

end StatMech.Walls
