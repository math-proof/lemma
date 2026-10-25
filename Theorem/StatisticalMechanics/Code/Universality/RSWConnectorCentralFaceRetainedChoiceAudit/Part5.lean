/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceRetainedChoiceAudit.Part5
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_retainedChoiceAudit_left_edges :
    rlc_pathEdges rlc_retainedChoiceAuditLeft.1 =
      rlc_rca_leftEdges := by
  simp [rlc_retainedChoiceAuditLeft, rlc_pathEdges,
    rlc_rca_leftWalk, rlc_rca_lv, rlc_rca_leftEdges,
    SimpleGraph.Walk.toPath, SimpleGraph.Walk.bypass]

theorem rlc_retainedChoiceAudit_faithful :
    RlcBookFaithfulTracePair
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [Finset.disjoint_left, rlc_retainedChoiceAudit_right_vertices,
      rlc_retainedChoiceAudit_left_vertices]
    simp
  · norm_num [rlc_retainedChoiceAuditRight, rlc_rca_rv]
  · change (0 : Int) < 2
    norm_num
  · intro z hz hz0
    change z = (![0, -2] : Site 2)
    rw [rlc_retainedChoiceAudit_right_vertices] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp at hz0 ⊢
  · intro z hz hz0
    change z = (![0, 2] : Site 2)
    rw [rlc_retainedChoiceAudit_left_vertices] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp at hz0 ⊢

end
end StatMech.Universality
