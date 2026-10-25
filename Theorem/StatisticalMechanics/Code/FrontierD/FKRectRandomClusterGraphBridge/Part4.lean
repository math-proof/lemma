/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionCharge.Part2
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge.Part3
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectFullGraphConfiguration_indexedEdge
    (R : FKRectTorus) (omega : R.Configuration) (a : R.EdgeIndex) :
    fkRectFullGraphConfiguration R omega
        (fkRectTorusIndexedEdge R a) = omega a := by
  classical
  unfold fkRectFullGraphConfiguration
  have he : fkRectTorusIndexedEdge R a ∈
      (fkRectTorusGraph R).edgeSet :=
    (mem_fkRectTorusGraph_edgeSet_iff R _).2 ⟨a, rfl⟩
  rw [dif_pos he]
  have h := (fkRectEdgeGraphEquiv R).apply_symm_apply
    ⟨fkRectTorusIndexedEdge R a, he⟩
  exact congrArg omega ((fkRectEdgeGraphEquiv R).injective
    (Subtype.ext (congrArg Subtype.val h)))

theorem fkRectFullGraphConfiguration_eq_false_of_not_edge
    (R : FKRectTorus) (omega : R.Configuration)
    {e : Sym2 R.Vertex} (he : e ∉ (fkRectTorusGraph R).edgeSet) :
    fkRectFullGraphConfiguration R omega e = false := by
  classical
  simp [fkRectFullGraphConfiguration, he]


theorem fkOpenSub_fullGraphConfiguration
    (R : FKRectTorus) (omega : R.Configuration) :
    StatMech.FK.openSub (fkRectTorusGraph R)
        (fkRectFullGraphConfiguration R omega) =
      fkRectOpenGraph R omega := by
  ext x y
  constructor
  · rintro ⟨hadj, hopen⟩
    obtain ⟨a, ha⟩ :=
      (mem_fkRectTorusGraph_edgeSet_iff R s(x, y)).1
        ((SimpleGraph.mem_edgeSet (fkRectTorusGraph R)).2 hadj)
    refine ⟨a, ?_, ha⟩
    rw [← fkRectFullGraphConfiguration_indexedEdge R omega a, ha]
    exact hopen
  · rintro ⟨a, hopen, ha⟩
    constructor
    · exact (SimpleGraph.mem_edgeSet (fkRectTorusGraph R)).1
        ((mem_fkRectTorusGraph_edgeSet_iff R _).2 ⟨a, ha⟩)
    · rw [← ha, fkRectFullGraphConfiguration_indexedEdge]
      exact hopen


end
end StatMech.FrontierD
