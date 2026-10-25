/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part7
open Finset SimpleGraph

set_option maxHeartbeats 800000


namespace StatMech.FrontierD

noncomputable section

open StatMech

@[simp] theorem mem_fkRectGraphEdgesOfIndices
    (R : FKRectTorus) (I : Finset R.EdgeIndex)
    (a : R.EdgeIndex) :
    fkRectEdgeGraphEquiv R a ∈ fkRectGraphEdgesOfIndices R I ↔ a ∈ I := by
  simp [fkRectGraphEdgesOfIndices]

@[simp] theorem fkRectGraphEdgesOfIndices_card
    (R : FKRectTorus) (I : Finset R.EdgeIndex) :
    (fkRectGraphEdgesOfIndices R I).card = I.card := by
  simp [fkRectGraphEdgesOfIndices]


theorem fkRectConfigurationGraphEquiv_forceEdgesClosed
    (R : FKRectTorus) (I : Finset R.EdgeIndex)
    (omega : R.Configuration) :
    fkRectConfigurationGraphEquiv R (fkRectForceEdgesClosed R I omega) =
      fkRectGraphForceClosed R (fkRectGraphEdgesOfIndices R I)
        (fkRectConfigurationGraphEquiv R omega) := by
  funext e
  let a := (fkRectEdgeGraphEquiv R).symm e
  have he : e = fkRectEdgeGraphEquiv R a := by
    exact ((fkRectEdgeGraphEquiv R).apply_symm_apply e).symm
  rw [he]
  by_cases ha : a ∈ I
  · simp [ha]
  · simp [ha]


theorem fkRectConfigurationGraphEquiv_forceEdgesOpen
    (R : FKRectTorus) (I : Finset R.EdgeIndex)
    (omega : R.Configuration) :
    fkRectConfigurationGraphEquiv R (fkRectForceEdgesOpen R I omega) =
      fkRectGraphForceOpen R (fkRectGraphEdgesOfIndices R I)
        (fkRectConfigurationGraphEquiv R omega) := by
  funext e
  let a := (fkRectEdgeGraphEquiv R).symm e
  have he : e = fkRectEdgeGraphEquiv R a := by
    exact ((fkRectEdgeGraphEquiv R).apply_symm_apply e).symm
  rw [he]
  by_cases ha : a ∈ I
  · simp [ha]
  · simp [ha]


end
end StatMech.FrontierD
