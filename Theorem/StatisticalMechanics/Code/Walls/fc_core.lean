/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Theorem.StatisticalMechanics.Code.Walls.fc_weightle
import Theorem.StatisticalMechanics.Code.Walls.fc_allclosed
import Theorem.StatisticalMechanics.Code.Walls.fc_bulkfraction
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


namespace StatMech

namespace Walls

open StatMech.FK StatMech.Lattice


section Boundedness

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem fc_fkZEdge_le_qpow {p q : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 1 ≤ q) :
    ecz_fkZEdge G p q ≤ (2 : ℝ) ^ G.edgeFinset.card * q ^ Fintype.card V := by
  unfold ecz_fkZEdge
  calc ∑ ω : ecz_ClosedOff G, fkWeight G p q ω.val
      ≤ ∑ ω : ecz_ClosedOff G, q ^ Fintype.card V :=
        Finset.sum_le_sum (fun ω _ => StatMech.Walls.FK.fc_fkWeight_le_qpow_card G hp hp1 hq ω.val)
    _ = (Fintype.card (ecz_ClosedOff G) : ℝ) * q ^ Fintype.card V := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (2 : ℝ) ^ G.edgeFinset.card * q ^ Fintype.card V := by
        rw [ecz_closedOff_card G]; push_cast; ring

end Boundedness
end Walls
end StatMech
