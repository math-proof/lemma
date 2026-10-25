/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingInsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingSubgroup.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerDefectLocalCriterion
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectClosedWindingSubgroup_mono_configurationOfEdges
    (R : FKRectTorus) {F A : Finset R.EdgeIndex} (hFA : F ⊆ A)
    (x : R.Vertex) :
    fkRectClosedWindingSubgroup R (fkRectConfigurationOfEdges R F) x ≤
      fkRectClosedWindingSubgroup R (fkRectConfigurationOfEdges R A) x := by
  rintro u ⟨p, rfl⟩
  have hgraph : fkRectOpenGraph R (fkRectConfigurationOfEdges R F) ≤
      fkRectOpenGraph R (fkRectConfigurationOfEdges R A) := by
    apply fkRectOpenGraph_mono R
    intro e he
    rw [fkRectConfigurationOfEdges_apply] at he ⊢
    exact hFA he
  exact ⟨p.mapLe hgraph, fkRectWalkWinding_mapLe R hgraph p⟩


theorem fkRectOpenGraph_le_insert
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex) :
    fkRectOpenGraph R (fkRectConfigurationOfEdges R F) ≤
      fkRectOpenGraph R (fkRectConfigurationOfEdges R (insert e F)) := by
  apply fkRectOpenGraph_mono R
  intro a ha
  rw [fkRectConfigurationOfEdges_apply] at ha ⊢
  exact Finset.mem_insert_of_mem ha


theorem fkRectOpenGraph_insert_adj_medialPrimals
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex) :
    (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R (insert e F))).Adj
        (fkRectMedialEastPrimal R e) (fkRectMedialWestPrimal R e) := by
  rw [fkRectOpenGraph_configurationOfEdges_insert R F e
    (fkRectTorusIndexedEdge_eq_medialPrimals R e)]
  right
  rw [SimpleGraph.edge_adj]
  have hne : fkRectMedialWestPrimal R e ≠
      fkRectMedialEastPrimal R e := by
    intro h
    apply fkRectTorusIndexedEdge_ne_diag R e
      (fkRectMedialWestPrimal R e)
    simpa [h] using fkRectTorusIndexedEdge_eq_medialPrimals R e
  exact ⟨Or.inr ⟨rfl, rfl⟩, hne.symm⟩


end
end StatMech.FrontierD
