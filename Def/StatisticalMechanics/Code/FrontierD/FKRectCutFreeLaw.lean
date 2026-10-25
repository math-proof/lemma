/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutFreeLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part6
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigEventLaw.Part2
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutFreeLaw
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


def fkRectCutClosedToEdgeConfig (R : FKRectTorus)
    (omega : FKRectCutClosedConfig R) :
    FK.ecz_ClosedOff (fkRectCutGraph R) :=
  ⟨fkRectFullGraphConfiguration R omega.1, by
    intro e he
    have hnotCutEdge : e ∉ (fkRectCutGraph R).edgeSet := by
      simpa only [SimpleGraph.mem_edgeFinset] using he
    by_cases htorus : e ∈ (fkRectTorusGraph R).edgeSet
    · obtain ⟨a, ha⟩ := (mem_fkRectTorusGraph_edgeSet_iff R e).1 htorus
      have hacut : a ∈ fkRectTorusCutEdges R := by
        by_contra hnot
        apply hnotCutEdge
        exact (mem_fkRectCutGraph_edgeSet_iff R e).2 ⟨a, hnot, ha⟩
      rw [← ha, fkRectFullGraphConfiguration_indexedEdge]
      exact (fkRectCutClosedConfiguration_iff R omega.1).1 omega.2 a hacut
    · exact fkRectFullGraphConfiguration_eq_false_of_not_edge
        R omega.1 htorus⟩


def fkRectEdgeConfigToCutClosed (R : FKRectTorus)
    (sigma : FK.ecz_ClosedOff (fkRectCutGraph R)) :
    FKRectCutClosedConfig R :=
  ⟨fun a => sigma.1 (fkRectTorusIndexedEdge R a),
    (fkRectCutClosedConfiguration_iff R _).2 (by
      intro a hacut
      apply sigma.2
      intro hedge
      have hedgeSet : fkRectTorusIndexedEdge R a ∈
          (fkRectCutGraph R).edgeSet := by
        simpa only [SimpleGraph.mem_edgeFinset] using hedge
      obtain ⟨b, hb, hba⟩ :=
        (mem_fkRectCutGraph_edgeSet_iff R _).1 hedgeSet
      exact hb ((fkRectTorusIndexedEdge_injective R hba).symm ▸ hacut))⟩


def fkRectCutClosedEdgeConfigEquiv (R : FKRectTorus) :
    FKRectCutClosedConfig R ≃ FK.ecz_ClosedOff (fkRectCutGraph R) where
  toFun := fkRectCutClosedToEdgeConfig R
  invFun := fkRectEdgeConfigToCutClosed R
  left_inv omega := by
    apply Subtype.ext
    funext a
    exact fkRectFullGraphConfiguration_indexedEdge R omega.1 a
  right_inv sigma := by
    apply Subtype.ext
    funext e
    change fkRectFullGraphConfiguration R
        (fkRectEdgeConfigToCutClosed R sigma).1 e = sigma.1 e
    by_cases htorus : e ∈ (fkRectTorusGraph R).edgeSet
    · obtain ⟨a, ha⟩ := (mem_fkRectTorusGraph_edgeSet_iff R e).1 htorus
      rw [← ha, fkRectFullGraphConfiguration_indexedEdge]
      rfl
    · rw [fkRectFullGraphConfiguration_eq_false_of_not_edge R _ htorus]
      symm
      apply sigma.2 e
      intro hedge
      have hedgeSet : e ∈ (fkRectCutGraph R).edgeSet := by
        simpa only [SimpleGraph.mem_edgeFinset] using hedge
      obtain ⟨a, _, ha⟩ := (mem_fkRectCutGraph_edgeSet_iff R e).1 hedgeSet
      exact htorus ((mem_fkRectTorusGraph_edgeSet_iff R e).2 ⟨a, ha⟩)

end
end StatMech.FrontierD
