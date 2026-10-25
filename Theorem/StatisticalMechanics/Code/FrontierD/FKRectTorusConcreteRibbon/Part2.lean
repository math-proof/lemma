/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusConcreteRibbon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRibbonClassification
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialClosedCycles.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusConcreteRibbon
open Equiv Finset


namespace StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

variable {T : EvenTorus}


theorem ribbonBoundaryPerm_insert_right
    {E D : Type*} [DecidableEq E] [Fintype D] [DecidableEq D]
    (S : RibbonPermutationSystem E D) (F : Finset E) (e : E)
    (he : e ∉ F) :
    S.boundaryPerm (insert e F) = S.boundaryPerm F * S.edgeFlip e := by
  have hcomm : Commute (S.edgeFlip e) (S.partialEdgeFlip F) := by
    unfold RibbonPermutationSystem.partialEdgeFlip
    apply Finset.noncommProd_commute
    intro f hf
    exact S.edgeFlip_commute e f fun h => he (h ▸ hf)
  rw [RibbonPermutationSystem.boundaryPerm,
    S.partialEdgeFlip_insert F e (by simpa using he),
    RibbonPermutationSystem.boundaryPerm]
  rw [hcomm.eq]
  simp only [mul_assoc]


theorem fkRectRibbonSystem_boundaryPerm
    (R : FKRectTorus) (F : Finset R.EdgeIndex) :
    (fkRectRibbonSystem R).boundaryPerm F =
      fkMedialBlackBoundaryPerm
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F)) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      rw [RibbonPermutationSystem.boundaryPerm_empty,
        fkRectConfigurationToMedialPairing_empty]
      rfl
  | @insert e F he ih =>
      rw [ribbonBoundaryPerm_insert_right (fkRectRibbonSystem R) F e he,
        fkRectConfigurationToMedialPairing_insert R F e he,
        fkMedialBlackBoundaryPerm_toggle, ih]
      rfl


theorem fkRectRibbonSystem_boundaryComponents
    (R : FKRectTorus) (F : Finset R.EdgeIndex) :
    (fkRectRibbonSystem R).boundaryComponents F =
      fkRectMedialLoopCount R (fkRectConfigurationOfEdges R F) := by
  unfold RibbonPermutationSystem.boundaryComponents fkRectMedialLoopCount
  rw [fkRectRibbonSystem_boundaryPerm,
    permCycleCount_fkMedialBlackBoundaryPerm]


end
end StatMech.FrontierD
