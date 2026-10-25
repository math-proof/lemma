/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingTailPrescribedCylinderTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectIndexedPatternPushforward.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderCrossings.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingCountBridge.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectWindingTailPrescribedCylinderTransfer.Part2
open Finset
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech

noncomputable section

theorem fkRectCriticalWindingTailMass_cFE_pow_le_prescribedCylinder
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q) (r : Nat)
    (I : Finset R.EdgeIndex) (pair : Fin R.width → Fin R.width)
    (S : Finset (Fin R.width))
    (hrepair : FKRectWindingTailPrescribedCylinderRepair
      R r I pair S) :
    FK.cFE (fkRectCriticalP q) q ^ I.card *
        fkRectCriticalWindingTailMass R q r ≤
      (2 ^ I.card : Nat) *
        StatMech.Probability.finiteEventMass
          (FK.fkProb (fkRectHorizontalCylinderGraph R)
            (fkRectCriticalP q) q)
          {rho | FKRectHorizontalCylinderDistinctPairedWitness
            R pair S rho} := by
  let A : Set R.Configuration :=
    {eta | FKRectHorizontalCylinderStablePairedWitnessCore R pair S eta}
  let Target : Set R.Configuration :=
    {eta | FKRectHorizontalCutClosedConfiguration R eta ∧ eta ∈ A}
  have htransfer :=
    fkRectCritical_cFE_pow_mul_event_le_two_pow_mul_of_localRepair
      R hq I
      {omega | r ≤ fkRectUnorientedVerticalWindingNumber R omega}
      Target (by
        intro omega homega
        exact hrepair omega homega)
  rw [← fkRectCriticalWindingTailMass_eq_eventMass] at htransfer
  have hcutNonneg := fkRectCriticalHorizontalCutEventMass_nonneg
    R hq A
  have htarget : fkRectCriticalEventMass R q Target ≤
      fkRectCriticalHorizontalCutEventMass R q A := by
    have heq := closedMass_mul_fkRectCriticalHorizontalCutEventMass
      R hq A
    have hclosed := fkRectCriticalClosedMass_horizontalCut_le_one R hq
    change fkRectCriticalEventMass R q
        {eta | FKRectHorizontalCutClosedConfiguration R eta ∧ eta ∈ A} ≤ _
    rw [← heq]
    exact mul_le_of_le_one_left hcutNonneg hclosed
  have hfactor : (0 : Real) ≤ (2 ^ I.card : Nat) := by positivity
  calc
    _ ≤ (2 ^ I.card : Nat) * fkRectCriticalEventMass R q Target :=
      htransfer
    _ ≤ (2 ^ I.card : Nat) *
        fkRectCriticalHorizontalCutEventMass R q A :=
      mul_le_mul_of_nonneg_left htarget hfactor
    _ = _ := by
      rw [fkRectCriticalHorizontalCut_stablePairedWitness_eq_finiteEventMass
        R pair hq S]


theorem fkRectCriticalWindingTailMass_cFE_perimeter_le_prescribedCylinder
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q) (r perimeter : Nat)
    (I : Finset R.EdgeIndex) (pair : Fin R.width → Fin R.width)
    (S : Finset (Fin R.width)) (hI : I.card ≤ perimeter)
    (hrepair : FKRectWindingTailPrescribedCylinderRepair
      R r I pair S) :
    FK.cFE (fkRectCriticalP q) q ^ perimeter *
        fkRectCriticalWindingTailMass R q r ≤
      (2 ^ perimeter : Nat) *
        StatMech.Probability.finiteEventMass
          (FK.fkProb (fkRectHorizontalCylinderGraph R)
            (fkRectCriticalP q) q)
          {rho | FKRectHorizontalCylinderDistinctPairedWitness
            R pair S rho} := by
  let cylinderMass := StatMech.Probability.finiteEventMass
    (FK.fkProb (fkRectHorizontalCylinderGraph R)
      (fkRectCriticalP q) q)
    {rho | FKRectHorizontalCylinderDistinctPairedWitness R pair S rho}
  have hbase :=
    fkRectCriticalWindingTailMass_cFE_pow_le_prescribedCylinder
      R hq r I pair S hrepair
  have hc : 0 ≤ FK.cFE (fkRectCriticalP q) q :=
    fkRectCritical_cFE_nonneg hq
  have hc1 : FK.cFE (fkRectCriticalP q) q ≤ 1 :=
    fkRectCritical_cFE_le_one hq
  have htail := fkRectCriticalWindingTailMass_nonneg
    R (lt_of_lt_of_le zero_lt_one hq) r
  have hcPow : FK.cFE (fkRectCriticalP q) q ^ perimeter ≤
      FK.cFE (fkRectCriticalP q) q ^ I.card :=
    pow_le_pow_of_le_one hc hc1 hI
  have htwoNat : 2 ^ I.card ≤ 2 ^ perimeter :=
    Nat.pow_le_pow_right (by omega) hI
  have htwo : ((2 ^ I.card : Nat) : Real) ≤
      ((2 ^ perimeter : Nat) : Real) := by
    exact_mod_cast htwoNat
  have hcylinder : 0 ≤ cylinderMass := by
    unfold cylinderMass StatMech.Probability.finiteEventMass
    apply Finset.sum_nonneg
    intro rho hrho
    split
    · exact FK.fkProb_nonneg
        (fkRectHorizontalCylinderGraph R)
        (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
        (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
        (lt_of_lt_of_le zero_lt_one hq) rho
    · exact le_rfl
  calc
    FK.cFE (fkRectCriticalP q) q ^ perimeter *
          fkRectCriticalWindingTailMass R q r ≤
        FK.cFE (fkRectCriticalP q) q ^ I.card *
          fkRectCriticalWindingTailMass R q r :=
      mul_le_mul_of_nonneg_right hcPow htail
    _ ≤ (2 ^ I.card : Nat) * cylinderMass := hbase
    _ ≤ (2 ^ perimeter : Nat) * cylinderMass :=
      mul_le_mul_of_nonneg_right htwo hcylinder


end
end StatMech.FrontierD
