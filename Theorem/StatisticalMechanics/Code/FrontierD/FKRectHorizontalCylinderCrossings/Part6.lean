/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderCrossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderLaw.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings.Part6
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectHorizontalCylinderStablePairedWitness_edgeEvent_eq
    (R : FKRectTorus) (pair : Fin R.width -> Fin R.width)
    (S : Finset (Fin R.width)) :
    FK.ecz_closeOff (fkRectHorizontalCylinderGraph R) ⁻¹'
        fkRectHorizontalCylinderEdgeEvent R
          {eta | FKRectHorizontalCylinderStablePairedWitnessCore
            R pair S eta} =
      {rho | FKRectHorizontalCylinderDistinctPairedWitness
        R pair S rho} := by
  ext rho
  let sigma := FK.ecz_closeOff (fkRectHorizontalCylinderGraph R) rho
  let eta :=
    (fkRectHorizontalCutClosedEdgeConfigEquiv R).symm sigma
  change FKRectHorizontalCylinderStablePairedWitnessCore
      R pair S eta.1 ↔ _
  have hclosed : fkRectForceHorizontalCutClosed R eta.1 = eta.1 :=
    fkRectHorizontalCutClosedConfiguration_force_eq_self
      R eta.1 eta.2
  unfold FKRectHorizontalCylinderStablePairedWitnessCore
  rw [hclosed]
  have hequiv :
      fkRectHorizontalCutClosedEdgeConfigEquiv R eta = sigma := by
    exact (fkRectHorizontalCutClosedEdgeConfigEquiv R).apply_symm_apply sigma
  have hval : fkRectFullGraphConfiguration R eta.1 = sigma.1 := by
    rw [← fkRectHorizontalCutClosedEdgeConfigEquiv_apply]
    exact congrArg Subtype.val hequiv
  rw [hval]
  apply FKRectHorizontalCylinderDistinctPairedWitness.congr_openSub
  exact openSub_ecz_closeOff_horizontalCylinder R rho


theorem fkRectCriticalHorizontalCut_stablePairedWitness_eq_finiteEventMass
    (R : FKRectTorus) (pair : Fin R.width -> Fin R.width)
    {q : Real} (hq : 1 <= q) (S : Finset (Fin R.width)) :
    fkRectCriticalHorizontalCutEventMass R q
        {eta | FKRectHorizontalCylinderStablePairedWitnessCore
          R pair S eta} =
      StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectHorizontalCylinderGraph R)
          (fkRectCriticalP q) q)
        {rho | FKRectHorizontalCylinderDistinctPairedWitness
          R pair S rho} := by
  rw [fkRectCriticalHorizontalCutEventMass_eq_cylinderGraph R hq,
    fkRectHorizontalCylinderStablePairedWitness_edgeEvent_eq]
  unfold StatMech.Probability.finiteEventMass
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hmem :
      FKRectHorizontalCylinderDistinctPairedWitness R pair S rho <;>
    simp [Set.indicator, hmem]

end
end StatMech.FrontierD
