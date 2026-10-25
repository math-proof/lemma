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
import Def.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamWindingUpper
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectCutMedialColumn_val
    (R : FKRectTorus) (x : Fin R.width) (b : Bool) :
    (fkRectCutMedialColumn R x b).val = b.toNat + 2 * x.val := by
  simp [fkRectCutMedialColumn]

@[simp] theorem fkRectCutMedialColumn_snd
    (R : FKRectTorus) (x : Fin R.width) (b : Bool) :
    (fkRectMedialVertexOfEdge R
      (b, (x, ⟨0, R.height_pos⟩))).2 = ⟨0, R.height_pos⟩ := by
  apply Fin.ext
  rfl

theorem fkRectCutMedialColumn_false_succ
    (R : FKRectTorus) (x : Fin R.width) :
    finitePeriodicSucc R.medialTorus.width_pos
        (fkRectCutMedialColumn R x false) =
      fkRectCutMedialColumn R x true := by
  apply Fin.ext
  rw [finitePeriodicSucc_val]
  have hne : 2 * x.val + 1 ≠ 2 * R.width := by omega
  simp [FKRectTorus.medialTorus, hne]
  omega

theorem fkRectTorusMedialEdgeEquiv_cutColumn
    (R : FKRectTorus) (x : Fin R.width) (b : Bool) :
    fkRectTorusMedialEdgeEquiv R
        (fkRectCutMedialColumn R x b, ⟨0, R.height_pos⟩) =
      (b, (x, ⟨0, R.height_pos⟩)) := by
  rw [show (fkRectCutMedialColumn R x b, ⟨0, R.height_pos⟩) =
      fkRectMedialVertexOfEdge R (b, (x, ⟨0, R.height_pos⟩)) by
    apply Prod.ext
    · rfl
    · apply Fin.ext; rfl]
  exact fkRectTorusMedialEdgeEquiv_vertexOfEdge R _


end
end StatMech.FrontierD
