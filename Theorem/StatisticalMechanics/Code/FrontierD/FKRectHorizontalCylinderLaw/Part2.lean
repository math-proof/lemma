/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCutPushforward.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutFreeLaw.Part4
import Instance.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderLaw.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


theorem fkRectHorizontalCylinderGraph_adj_iff
    (R : FKRectTorus) (x y : R.Vertex) :
    (fkRectHorizontalCylinderGraph R).Adj x y ↔
      (fkRectTorusGraph R).Adj x y ∧
        s(x, y) ∉ fkRectHorizontalCutGraphEdges R := by
  rw [fkRectHorizontalCylinderGraph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨hedge, hcut⟩, _⟩
    exact ⟨(SimpleGraph.mem_edgeSet (fkRectTorusGraph R)).1 hedge, hcut⟩
  · rintro ⟨hxy, hcut⟩
    exact ⟨⟨(SimpleGraph.mem_edgeSet (fkRectTorusGraph R)).2 hxy,
      hcut⟩, hxy.ne⟩


theorem mem_fkRectHorizontalCylinderGraph_edgeSet_iff
    (R : FKRectTorus) (e : Sym2 R.Vertex) :
    e ∈ (fkRectHorizontalCylinderGraph R).edgeSet ↔
      ∃ a : R.EdgeIndex,
        a ∉ fkRectHorizontalCutEdges R ∧
          fkRectTorusIndexedEdge R a = e := by
  obtain ⟨⟨x, y⟩, rfl⟩ := Quot.exists_rep e
  rw [SimpleGraph.mem_edgeSet, fkRectHorizontalCylinderGraph_adj_iff]
  constructor
  · rintro ⟨htorus, hcut⟩
    obtain ⟨a, ha⟩ := htorus
    refine ⟨a, ?_, ha⟩
    intro hacut
    apply hcut
    rw [← ha]
    exact (mem_fkRectHorizontalCutGraphEdges R a).2 hacut
  · rintro ⟨a, hacut, ha⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    intro hcut
    have hcut' : fkRectTorusIndexedEdge R a ∈
        fkRectHorizontalCutGraphEdges R := by
      simpa only [ha] using hcut
    exact hacut ((mem_fkRectHorizontalCutGraphEdges R a).1 hcut')


end
end StatMech.FrontierD
