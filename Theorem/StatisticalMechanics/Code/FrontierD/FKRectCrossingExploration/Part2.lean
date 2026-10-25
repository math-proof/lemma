/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalDualCrossings.Part7
import Theorem.StatisticalMechanics.Code.Probability.FiniteWitnessUnionBound
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreFreeDomination.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem mem_fkRectTorusCutGraphEdges
    (R : FKRectTorus) (a : R.EdgeIndex) :
    fkRectTorusIndexedEdge R a ∈ fkRectTorusCutGraphEdges R ↔
      a ∈ fkRectTorusCutEdges R := by
  classical
  unfold fkRectTorusCutGraphEdges
  rw [Finset.mem_image]
  constructor
  · rintro ⟨b, hb, hab⟩
    exact (fkRectTorusIndexedEdge_injective R hab).symm ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

theorem fkRectFullGraphConfiguration_forceCut_eq_false_of_cutEdge
    (R : FKRectTorus) (eta : R.Configuration)
    {e : Sym2 R.Vertex} (he : e ∈ fkRectTorusCutGraphEdges R) :
    fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta) e = false := by
  classical
  rw [fkRectTorusCutGraphEdges, Finset.mem_image] at he
  rcases he with ⟨a, ha, rfl⟩
  rw [fkRectFullGraphConfiguration_indexedEdge,
    fkRectForceCutClosed_of_mem R eta a ha]


end
end StatMech.FrontierD
