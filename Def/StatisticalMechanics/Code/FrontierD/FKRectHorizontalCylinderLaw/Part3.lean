/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCutPushforward.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutFreeLaw.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderLaw.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


def fkRectHorizontalCutClosedToEdgeConfig (R : FKRectTorus)
    (omega : FKRectHorizontalCutClosedConfig R) :
    FK.ecz_ClosedOff (fkRectHorizontalCylinderGraph R) :=
  ⟨fkRectFullGraphConfiguration R omega.1, by
    intro e he
    have hnotCylinder : e ∉
        (fkRectHorizontalCylinderGraph R).edgeSet := by
      simpa only [SimpleGraph.mem_edgeFinset] using he
    by_cases htorus : e ∈ (fkRectTorusGraph R).edgeSet
    · obtain ⟨a, ha⟩ :=
        (mem_fkRectTorusGraph_edgeSet_iff R e).1 htorus
      have hacut : a ∈ fkRectHorizontalCutEdges R := by
        by_contra hnot
        apply hnotCylinder
        exact (mem_fkRectHorizontalCylinderGraph_edgeSet_iff R e).2
          ⟨a, hnot, ha⟩
      rw [← ha, fkRectFullGraphConfiguration_indexedEdge]
      exact omega.2 a hacut
    · exact fkRectFullGraphConfiguration_eq_false_of_not_edge
        R omega.1 htorus⟩


def fkRectEdgeConfigToHorizontalCutClosed (R : FKRectTorus)
    (sigma : FK.ecz_ClosedOff (fkRectHorizontalCylinderGraph R)) :
    FKRectHorizontalCutClosedConfig R :=
  ⟨fun a => sigma.1 (fkRectTorusIndexedEdge R a), by
    intro a hacut
    apply sigma.2
    intro hedge
    have hedgeSet : fkRectTorusIndexedEdge R a ∈
        (fkRectHorizontalCylinderGraph R).edgeSet := by
      simpa only [SimpleGraph.mem_edgeFinset] using hedge
    obtain ⟨b, hb, hba⟩ :=
      (mem_fkRectHorizontalCylinderGraph_edgeSet_iff R _).1 hedgeSet
    exact hb ((fkRectTorusIndexedEdge_injective R hba).symm ▸ hacut)⟩


def fkRectHorizontalCutClosedEdgeConfigEquiv (R : FKRectTorus) :
    FKRectHorizontalCutClosedConfig R ≃
      FK.ecz_ClosedOff (fkRectHorizontalCylinderGraph R) where
  toFun := fkRectHorizontalCutClosedToEdgeConfig R
  invFun := fkRectEdgeConfigToHorizontalCutClosed R
  left_inv omega := by
    apply Subtype.ext
    funext a
    exact fkRectFullGraphConfiguration_indexedEdge R omega.1 a
  right_inv sigma := by
    apply Subtype.ext
    funext e
    change fkRectFullGraphConfiguration R
        (fkRectEdgeConfigToHorizontalCutClosed R sigma).1 e = sigma.1 e
    by_cases htorus : e ∈ (fkRectTorusGraph R).edgeSet
    · obtain ⟨a, ha⟩ :=
        (mem_fkRectTorusGraph_edgeSet_iff R e).1 htorus
      rw [← ha, fkRectFullGraphConfiguration_indexedEdge]
      rfl
    · rw [fkRectFullGraphConfiguration_eq_false_of_not_edge R _ htorus]
      symm
      apply sigma.2 e
      intro hedge
      have hedgeSet : e ∈
          (fkRectHorizontalCylinderGraph R).edgeSet := by
        simpa only [SimpleGraph.mem_edgeFinset] using hedge
      obtain ⟨a, _, ha⟩ :=
        (mem_fkRectHorizontalCylinderGraph_edgeSet_iff R e).1 hedgeSet
      exact htorus ((mem_fkRectTorusGraph_edgeSet_iff R e).2 ⟨a, ha⟩)

end
end StatMech.FrontierD
