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
import Instance.StatisticalMechanics.Code.FrontierD.FKRectCutFreeLaw
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


theorem mem_fkRectCutGraph_edgeSet_iff (R : FKRectTorus)
    (e : Sym2 R.Vertex) :
    e ∈ (fkRectCutGraph R).edgeSet ↔
      ∃ a : R.EdgeIndex,
        a ∉ fkRectTorusCutEdges R ∧ fkRectTorusIndexedEdge R a = e := by
  obtain ⟨⟨x, y⟩, rfl⟩ := Quot.exists_rep e
  rw [SimpleGraph.mem_edgeSet, fkRectCutGraph_adj_iff]
  constructor
  · rintro ⟨htorus, hcut⟩
    obtain ⟨a, ha⟩ := htorus
    refine ⟨a, ?_, ha⟩
    intro hacut
    apply hcut
    rw [← ha, mem_fkRectTorusCutGraphEdges]
    exact hacut
  · rintro ⟨a, hacut, ha⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    intro hcut
    have hcut' : fkRectTorusIndexedEdge R a ∈
        fkRectTorusCutGraphEdges R := by
      simpa only [ha] using hcut
    exact hacut ((mem_fkRectTorusCutGraphEdges R a).1 hcut')


end
end StatMech.FrontierD
