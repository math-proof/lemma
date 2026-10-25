/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamWindingUpper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamBarrier.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRankOneWindingTail
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryVerticalFlux.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAugmentedBarrierPatternCost
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamWindingUpper
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectCutMedialColumnEquiv (R : FKRectTorus) :
    Fin R.width × Bool ≃ Fin R.medialTorus.width where
  toFun xb := fkRectCutMedialColumn R xb.1 xb.2
  invFun i :=
    ((fkRectTorusMedialEdgeEquiv R (i, ⟨0, R.height_pos⟩)).2.1,
      (fkRectTorusMedialEdgeEquiv R (i, ⟨0, R.height_pos⟩)).1)
  left_inv := by
    rintro ⟨x, b⟩
    change ((fkRectTorusMedialEdgeEquiv R
        (fkRectCutMedialColumn R x b, ⟨0, R.height_pos⟩)).2.1,
      (fkRectTorusMedialEdgeEquiv R
        (fkRectCutMedialColumn R x b, ⟨0, R.height_pos⟩)).1) = (x, b)
    rw [show fkRectTorusMedialEdgeEquiv R
        (fkRectCutMedialColumn R x b, ⟨0, R.height_pos⟩) =
      (b, (x, ⟨0, R.height_pos⟩)) from
        fkRectTorusMedialEdgeEquiv_cutColumn R x b]
  right_inv := by
    intro i
    let e := fkRectTorusMedialEdgeEquiv R
      (i, ⟨0, R.height_pos⟩)
    have he : fkRectMedialVertexOfEdge R e =
        (i, ⟨0, R.height_pos⟩) := by
      exact (fkRectTorusMedialEdgeEquiv R).symm_apply_apply _
    change fkRectCutMedialColumn R e.2.1 e.1 = i
    unfold fkRectCutMedialColumn
    have hbase : e.2.2 = ⟨0, R.height_pos⟩ := by
      have hsnd := congrArg Prod.snd he
      exact hsnd
    rw [← hbase]
    exact congrArg Prod.fst he


end
end StatMech.FrontierD
