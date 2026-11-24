module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRibbonCounts.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
public import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusEdgeFinset.Part2
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEdgeFinset.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

theorem fkRectOpenEdgeCount_configurationOfEdges
    (R : FKRectTorus) (F : Finset R.EdgeIndex) :
    fkRectOpenEdgeCount R (fkRectConfigurationOfEdges R F) = F.card := by
  unfold fkRectOpenEdgeCount
  rw [show (Finset.univ.filter fun a : R.EdgeIndex =>
      fkRectConfigurationOfEdges R F a = true) = F by
    simpa [fkRectOpenEdges] using fkRectOpenEdges_configurationOfEdges R F]

@[simp] theorem fkRectOpenGraph_configurationOfEdges_adj
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (x y : R.Vertex) :
    (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Adj x y ↔
      ∃ a ∈ F, fkRectTorusIndexedEdge R a = s(x, y) := by
  simp [fkRectOpenGraph, fkRectConfigurationOfEdges]

theorem fkRectOpenGraph_configurationOfEdges_empty (R : FKRectTorus) :
    fkRectOpenGraph R (fkRectConfigurationOfEdges R ∅) = ⊥ := by
  ext x y
  simp

theorem fkRectOpenGraph_configurationOfEdges_univ (R : FKRectTorus) :
    fkRectOpenGraph R (fkRectConfigurationOfEdges R Finset.univ) =
      fkRectTorusGraph R := by
  ext x y
  simp [fkRectTorusGraph]


end
end StatMech.FrontierD
