/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceConnected.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveMixedNoLoopHeight
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice.Part9
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceNoLoop


namespace StatMech.FrontierD

noncomputable section

open Filter Topology


theorem fkRectForcedDualSameSideRightBoundaryConnected_of_reflection
    (R : FKRectTorus) (omega : R.Configuration)
    (hreflect :
      FKRectForcedDualSameSideRightBoundaryConnectivityReflection R omega) :
    FKRectForcedDualSameSideRightBoundaryConnected R omega := by
  intro C D X hCbranch hDbranch hCX hDX hside
  obtain ⟨yC, hyC⟩ :=
    fkRectZeroTurnDualRightBoundaryContacts_nonempty R omega C
  obtain ⟨yD, hyD⟩ :=
    fkRectZeroTurnDualRightBoundaryContacts_nonempty R omega D
  refine ⟨yC, yD, hyC, hyD, ?_⟩
  apply hreflect C D X hCbranch hDbranch hCX hDX hside yC yD hyC hyD
  exact fkRectDualOpenGraph_rightBoundary_reachable R
    (fkRectForceCutClosed R omega)
    (fkRectCutClosedConfiguration_forceCutClosed R omega) yC yD

set_option maxHeartbeats 800000 in


theorem
    fkRectBlackBoundaryCyclePrimalComponent_dualEquiv_eq_of_rightBoundaryContacts_reachable
    (R : FKRectTorus) (omega : R.Configuration)
    (C D : FKRectZeroTurnCutRemainderComponent R omega)
    (yC yD : Fin R.height)
    (hyC : yC ∈ fkRectZeroTurnDualRightBoundaryContacts R omega C)
    (hyD : yD ∈ fkRectZeroTurnDualRightBoundaryContacts R omega D)
    (hyCD : (fkRectOpenGraph R
      (fkRectDualConfigurationEquiv R omega)).Reachable
        (fkRectRightColumn R, yC) (fkRectRightColumn R, yD)) :
    fkRectBlackBoundaryCyclePrimalComponent R
        (fkRectDualConfigurationEquiv R omega)
        (fkRectBlackBoundaryCycleDualEquiv R omega
          (Quot.mk _ (fkRectZeroTurnRemainderBlackDart R omega C))) =
      fkRectBlackBoundaryCyclePrimalComponent R
        (fkRectDualConfigurationEquiv R omega)
        (fkRectBlackBoundaryCycleDualEquiv R omega
          (Quot.mk _ (fkRectZeroTurnRemainderBlackDart R omega D))) := by
  let eta := fkRectDualConfigurationEquiv R omega
  let bC := fkRectZeroTurnRemainderBlackDart R omega C
  let bD := fkRectZeroTurnRemainderBlackDart R omega D
  let sC := fkRectMedialDualShiftDart R bC.1
  let sD := fkRectMedialDualShiftDart R bD.1
  let zC : R.Vertex := (fkRectRightColumn R, yC)
  let zD : R.Vertex := (fkRectRightColumn R, yD)
  have hzC : zC ∈
      (fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega C).support :=
    (mem_fkRectZeroTurnDualRightBoundaryContacts R omega C yC).1 hyC
  have hzD : zD ∈
      (fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega D).support :=
    (mem_fkRectZeroTurnDualRightBoundaryContacts R omega D yD).1 hyD
  have hCstart : (fkRectOpenGraph R eta).Reachable
      (fkRectMedialDartPrimalLabel R
        (fkRectDualBlackDartEquiv R omega bC).1) zC := by
    have hpC : (fkRectOpenGraph R eta).Reachable
        (fkRectMedialDartPrimalLabel R sC) zC := by
      simpa [eta, sC, bC, zC] using
        ((fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega C).takeUntil
          zC hzC).reachable
    have hlocal := fkRectMedialDartPrimalLabel_localMate_reachable
      R eta sC
    simpa [eta, sC, bC, fkRectDualBlackDartEquiv] using
      hlocal.symm.trans hpC
  have hDstart : (fkRectOpenGraph R eta).Reachable
      (fkRectMedialDartPrimalLabel R
        (fkRectDualBlackDartEquiv R omega bD).1) zD := by
    have hpD : (fkRectOpenGraph R eta).Reachable
        (fkRectMedialDartPrimalLabel R sD) zD := by
      simpa [eta, sD, bD, zD] using
        ((fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega D).takeUntil
          zD hzD).reachable
    have hlocal := fkRectMedialDartPrimalLabel_localMate_reachable
      R eta sD
    simpa [eta, sD, bD, fkRectDualBlackDartEquiv] using
      hlocal.symm.trans hpD
  rw [fkRectBlackBoundaryCycleDualEquiv_mk,
    fkRectBlackBoundaryCycleDualEquiv_mk,
    fkRectBlackBoundaryCyclePrimalComponent_mk,
    fkRectBlackBoundaryCyclePrimalComponent_mk]
  apply SimpleGraph.ConnectedComponent.sound
  exact hCstart.trans (hyCD.trans hDstart.symm)


theorem
    fkRectBlackBoundaryCyclePrimalComponent_dualEquiv_eq_of_sharedRightBoundaryContact
    (R : FKRectTorus) (omega : R.Configuration)
    (C D : FKRectZeroTurnCutRemainderComponent R omega)
    (y : Fin R.height)
    (hyC : y ∈ fkRectZeroTurnDualRightBoundaryContacts R omega C)
    (hyD : y ∈ fkRectZeroTurnDualRightBoundaryContacts R omega D) :
    fkRectBlackBoundaryCyclePrimalComponent R
        (fkRectDualConfigurationEquiv R omega)
        (fkRectBlackBoundaryCycleDualEquiv R omega
          (Quot.mk _ (fkRectZeroTurnRemainderBlackDart R omega C))) =
      fkRectBlackBoundaryCyclePrimalComponent R
        (fkRectDualConfigurationEquiv R omega)
        (fkRectBlackBoundaryCycleDualEquiv R omega
          (Quot.mk _ (fkRectZeroTurnRemainderBlackDart R omega D))) := by
  apply
    fkRectBlackBoundaryCyclePrimalComponent_dualEquiv_eq_of_rightBoundaryContacts_reachable
      R omega C D y y hyC hyD
  exact SimpleGraph.Reachable.refl _


theorem fkRectBlackBoundaryCycle_eq_of_primalComponent_eq_of_fst_mul_pos
    (R : FKRectTorus) (omega : R.Configuration)
    (C D : FKRectConfigurationBlackBoundaryCycle R omega)
    (hcomponent : fkRectBlackBoundaryCyclePrimalComponent R omega C =
      fkRectBlackBoundaryCyclePrimalComponent R omega D)
    (hsign : 0 < (fkRectBlackBoundaryCycleWinding R omega C).1 *
      (fkRectBlackBoundaryCycleWinding R omega D).1) :
    C = D := by
  classical
  induction C using Quot.ind with
  | _ c =>
      induction D using Quot.ind with
      | _ d =>
          let x := fkRectMedialDartPrimalLabel R c.1
          have hmemC : fkRectBlackBoundaryCycleInPrimalCluster R omega x
              (Quot.mk _ c) := by
            rw [fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent]
            simp [x, fkRectBlackBoundaryCyclePrimalComponent]
          have hmemD : fkRectBlackBoundaryCycleInPrimalCluster R omega x
              (Quot.mk _ d) := by
            rw [fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent]
            exact hcomponent.symm.trans
              ((fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent
                R omega x (Quot.mk _ c)).mp hmemC)
          exact fkRectBlackBoundaryCycle_eq_of_card_nonzero_le_two_of_fst_mul_pos
            R omega x
              (card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_atVertex
                R omega x)
              hmemC hmemD hsign


theorem fkRectZeroTurnRemainderBlackDart_fst_mul_pos_of_sameSide
    (R : FKRectTorus) (omega : R.Configuration)
    (C D : FKRectZeroTurnCutRemainderComponent R omega)
    (hside : fkRectZeroTurnRemainderSide R omega C =
      fkRectZeroTurnRemainderSide R omega D) :
    0 < (fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega
            (fkRectZeroTurnRemainderBlackDart R omega C))).1 *
        (fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega
            (fkRectZeroTurnRemainderBlackDart R omega D))).1 := by
  cases hCside : fkRectZeroTurnRemainderSide R omega C
  · have hDside : fkRectZeroTurnRemainderSide R omega D = false := by
      rw [← hside, hCside]
    exact mul_pos_of_neg_of_neg
      ((fkRectZeroTurnRemainderSide_eq_false_iff R omega C).mp hCside)
      ((fkRectZeroTurnRemainderSide_eq_false_iff R omega D).mp hDside)
  · have hDside : fkRectZeroTurnRemainderSide R omega D = true := by
      rw [← hside, hCside]
    exact mul_pos
      ((fkRectZeroTurnRemainderSide_eq_true_iff R omega C).mp hCside)
      ((fkRectZeroTurnRemainderSide_eq_true_iff R omega D).mp hDside)


theorem fkRectZeroTurnRemainder_eq_of_primalComponent_eq_of_sameSide
    (R : FKRectTorus) (omega : R.Configuration)
    (C D : FKRectZeroTurnCutRemainderComponent R omega)
    (hcomponent : fkRectZeroTurnRemainderPrimalComponent R omega C =
      fkRectZeroTurnRemainderPrimalComponent R omega D)
    (hside : fkRectZeroTurnRemainderSide R omega C =
      fkRectZeroTurnRemainderSide R omega D) :
    C = D := by
  let bC := fkRectZeroTurnRemainderBlackDart R omega C
  let bD := fkRectZeroTurnRemainderBlackDart R omega D
  let cC : FKRectConfigurationBlackBoundaryCycle R omega := Quot.mk _ bC
  let cD : FKRectConfigurationBlackBoundaryCycle R omega := Quot.mk _ bD
  have hcycleComponent :
      fkRectBlackBoundaryCyclePrimalComponent R omega cC =
        fkRectBlackBoundaryCyclePrimalComponent R omega cD := by
    calc
      fkRectBlackBoundaryCyclePrimalComponent R omega cC =
          (fkRectOpenGraph R omega).connectedComponentMk
            (fkRectMedialDartPrimalLabel R bC.1) := by
              simp [cC]
      _ = fkRectZeroTurnRemainderPrimalComponent R omega C :=
        (fkRectZeroTurnRemainderPrimalComponent_eq_label R omega C).symm
      _ = fkRectZeroTurnRemainderPrimalComponent R omega D := hcomponent
      _ = (fkRectOpenGraph R omega).connectedComponentMk
            (fkRectMedialDartPrimalLabel R bD.1) :=
        fkRectZeroTurnRemainderPrimalComponent_eq_label R omega D
      _ = fkRectBlackBoundaryCyclePrimalComponent R omega cD := by
        simp [cD]
  have hcycleSign : 0 <
      (fkRectBlackBoundaryCycleWinding R omega cC).1 *
        (fkRectBlackBoundaryCycleWinding R omega cD).1 := by
    rw [show cC = Quot.mk _ bC from rfl,
      show cD = Quot.mk _ bD from rfl,
      fkRectBlackBoundaryCycleWinding_mk,
      fkRectBlackBoundaryCycleWinding_mk,
      ← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass R omega bC,
      ← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass R omega bD]
    exact fkRectZeroTurnRemainderBlackDart_fst_mul_pos_of_sameSide
      R omega C D hside
  have hcycleEq : cC = cD :=
    fkRectBlackBoundaryCycle_eq_of_primalComponent_eq_of_fst_mul_pos
      R omega cC cD hcycleComponent hcycleSign
  have hsame : (fkMedialBlackBoundaryPerm
      (fkRectConfigurationToMedialPairing R omega)).SameCycle bC bD :=
    Quotient.exact hcycleEq
  apply Subtype.ext
  calc
    C.1 = (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          bC.1 := (fkRectZeroTurnRemainderBlackDart_component R omega C).symm
    _ = (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          bD.1 := by
      apply SimpleGraph.ConnectedComponent.sound
      exact (fkMedial_blackBoundary_sameCycle_iff_reachable _ _ _).mp hsame
    _ = D.1 := fkRectZeroTurnRemainderBlackDart_component R omega D


theorem fkRectZeroTurnRemainder_eq_of_dualComponent_eq_of_sameSide
    (R : FKRectTorus) (omega : R.Configuration)
    (C D : FKRectZeroTurnCutRemainderComponent R omega)
    (hcomponent :
      fkRectBlackBoundaryCyclePrimalComponent R
          (fkRectDualConfigurationEquiv R omega)
          (fkRectBlackBoundaryCycleDualEquiv R omega
            (Quot.mk _ (fkRectZeroTurnRemainderBlackDart R omega C))) =
        fkRectBlackBoundaryCyclePrimalComponent R
          (fkRectDualConfigurationEquiv R omega)
          (fkRectBlackBoundaryCycleDualEquiv R omega
            (Quot.mk _ (fkRectZeroTurnRemainderBlackDart R omega D))))
    (hside : fkRectZeroTurnRemainderSide R omega C =
      fkRectZeroTurnRemainderSide R omega D) :
    C = D := by
  let eta := fkRectDualConfigurationEquiv R omega
  let bC := fkRectZeroTurnRemainderBlackDart R omega C
  let bD := fkRectZeroTurnRemainderBlackDart R omega D
  let cC : FKRectConfigurationBlackBoundaryCycle R omega := Quot.mk _ bC
  let cD : FKRectConfigurationBlackBoundaryCycle R omega := Quot.mk _ bD
  let dcC := fkRectBlackBoundaryCycleDualEquiv R omega cC
  let dcD := fkRectBlackBoundaryCycleDualEquiv R omega cD
  have horigSign : 0 <
      (fkRectBlackBoundaryCycleWinding R omega cC).1 *
        (fkRectBlackBoundaryCycleWinding R omega cD).1 := by
    rw [show cC = Quot.mk _ bC from rfl,
      show cD = Quot.mk _ bD from rfl,
      fkRectBlackBoundaryCycleWinding_mk,
      fkRectBlackBoundaryCycleWinding_mk,
      ← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass R omega bC,
      ← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass R omega bD]
    exact fkRectZeroTurnRemainderBlackDart_fst_mul_pos_of_sameSide
      R omega C D hside
  have hdualSign : 0 <
      (fkRectBlackBoundaryCycleWinding R eta dcC).1 *
        (fkRectBlackBoundaryCycleWinding R eta dcD).1 := by
    change 0 <
      (fkRectBlackBoundaryCycleWinding R
        (fkRectDualConfigurationEquiv R omega) dcC).1 *
      (fkRectBlackBoundaryCycleWinding R
        (fkRectDualConfigurationEquiv R omega) dcD).1
    rw [show dcC = fkRectBlackBoundaryCycleDualEquiv R omega cC from rfl,
      show dcD = fkRectBlackBoundaryCycleDualEquiv R omega cD from rfl,
      fkRectBlackBoundaryCycleWinding_dualEquiv,
      fkRectBlackBoundaryCycleWinding_dualEquiv]
    simpa using horigSign
  have hdualEq : dcC = dcD :=
    fkRectBlackBoundaryCycle_eq_of_primalComponent_eq_of_fst_mul_pos
      R eta dcC dcD hcomponent hdualSign
  have horigEq : cC = cD :=
    (fkRectBlackBoundaryCycleDualEquiv R omega).injective hdualEq
  have hsame : (fkMedialBlackBoundaryPerm
      (fkRectConfigurationToMedialPairing R omega)).SameCycle bC bD :=
    Quotient.exact horigEq
  apply Subtype.ext
  calc
    C.1 = (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          bC.1 := (fkRectZeroTurnRemainderBlackDart_component R omega C).symm
    _ = (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          bD.1 := by
      apply SimpleGraph.ConnectedComponent.sound
      exact (fkMedial_blackBoundary_sameCycle_iff_reachable _ _ _).mp hsame
    _ = D.1 := fkRectZeroTurnRemainderBlackDart_component R omega D


end
end StatMech.FrontierD
