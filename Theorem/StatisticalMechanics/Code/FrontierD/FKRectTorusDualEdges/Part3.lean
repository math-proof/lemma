/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDualEdges.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges.Part3


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectDualConfigurationEquiv_apply
    (R : FKRectTorus) (omega : R.Configuration) (e : R.EdgeIndex) :
    fkRectDualConfigurationEquiv R omega e =
      !(omega (fkRectDualEdgeToEdge R e)) := rfl

theorem fkRectDualConfigurationEquiv_apply_edgeToDualEdge
    (R : FKRectTorus) (omega : R.Configuration) (e : R.EdgeIndex) :
    fkRectDualConfigurationEquiv R omega (fkRectEdgeToDualEdge R e) =
      !(omega e) := by
  simp

theorem fkRectDualConfiguration_open_iff_primal_closed
    (R : FKRectTorus) (omega : R.Configuration) (e : R.EdgeIndex) :
    fkRectDualConfigurationEquiv R omega (fkRectEdgeToDualEdge R e) = true ↔
      omega e = false := by
  rw [fkRectDualConfigurationEquiv_apply_edgeToDualEdge]
  cases omega e <;> simp


theorem fkRectDualConfigurationEquiv_antitone (R : FKRectTorus) :
    Antitone (fkRectDualConfigurationEquiv R) := by
  intro omega tau hot e
  rw [fkRectDualConfigurationEquiv_apply,
    fkRectDualConfigurationEquiv_apply]
  have h := hot (fkRectDualEdgeToEdge R e)
  cases homega : omega (fkRectDualEdgeToEdge R e) <;>
    cases htau : tau (fkRectDualEdgeToEdge R e) <;>
    simp_all

end
end StatMech.FrontierD
