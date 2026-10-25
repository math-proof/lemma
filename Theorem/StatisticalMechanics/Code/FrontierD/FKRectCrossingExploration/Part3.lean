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
import Instance.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration.Part2


namespace StatMech.FrontierD

noncomputable section

theorem fkRectCutGraph_adj_iff
    (R : FKRectTorus) (x y : R.Vertex) :
    (fkRectCutGraph R).Adj x y ↔
      (fkRectTorusGraph R).Adj x y ∧
        s(x, y) ∉ fkRectTorusCutGraphEdges R := by
  rw [fkRectCutGraph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨hedge, hcut⟩, _⟩
    exact ⟨(SimpleGraph.mem_edgeSet (fkRectTorusGraph R)).1 hedge, hcut⟩
  · rintro ⟨hxy, hcut⟩
    exact ⟨⟨(SimpleGraph.mem_edgeSet (fkRectTorusGraph R)).2 hxy,
      hcut⟩, hxy.ne⟩


end
end StatMech.FrontierD
