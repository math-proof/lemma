/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEdgeFinset.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRibbonCounts.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusEdgeFinset
open Finset SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

@[simp] theorem fkRectConfigurationOfEdges_apply
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (a : R.EdgeIndex) :
    fkRectConfigurationOfEdges R F a = true ↔ a ∈ F := by
  simp [fkRectConfigurationOfEdges]

@[simp] theorem fkRectOpenEdges_configurationOfEdges
    (R : FKRectTorus) (F : Finset R.EdgeIndex) :
    fkRectOpenEdges R (fkRectConfigurationOfEdges R F) = F := by
  classical
  ext a
  simp [fkRectOpenEdges]

@[simp] theorem fkRectConfigurationOfEdges_openEdges
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectConfigurationOfEdges R (fkRectOpenEdges R omega) = omega := by
  classical
  funext a
  cases h : omega a <;> simp [fkRectConfigurationOfEdges, fkRectOpenEdges, h]


end
end StatMech.FrontierD
