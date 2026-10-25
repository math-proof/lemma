/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleMerge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Def.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice
open Finset


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem mem_fkRectDualCutEdges_iff
    (R : FKRectTorus) (e : R.EdgeIndex) :
    e ∈ fkRectDualCutEdges R ↔
      fkRectDualEdgeToEdge R e ∈ fkRectTorusCutEdges R := by
  classical
  constructor
  · intro he
    rw [fkRectDualCutEdges, Finset.mem_image] at he
    obtain ⟨a, ha, rfl⟩ := he
    simpa using ha
  · intro he
    rw [fkRectDualCutEdges, Finset.mem_image]
    exact ⟨fkRectDualEdgeToEdge R e, he, by simp⟩


end
end StatMech.FrontierD
