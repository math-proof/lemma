/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleMerge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Def.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem fkRectDualRightBoundaryEdge_mem_dualCutEdges
    (R : FKRectTorus) (y : Fin R.height) :
    fkRectDualRightBoundaryEdge R y ∈ fkRectDualCutEdges R := by
  rw [mem_fkRectDualCutEdges_iff]
  simp only [fkRectDualRightBoundaryEdge, fkRectDualEdgeToEdge, ↓reduceIte]
  rw [finitePeriodicSucc_fkRectRightColumn]
  rw [mem_fkRectTorusCutEdges_iff]
  exact Or.inr ⟨rfl, rfl⟩


end
end StatMech.FrontierD
