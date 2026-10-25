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
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceNoLoop.Part7


namespace StatMech.FrontierD

noncomputable section

open Filter Topology


theorem fkRectForcedDualSameSideOriginalComponent_of_rightBoundaryConnected
    (R : FKRectTorus) (omega : R.Configuration)
    (hconnected : FKRectForcedDualSameSideRightBoundaryConnected R omega) :
    FKRectForcedDualSameSideOriginalComponent R omega := by
  intro C D X hCbranch hDbranch hCX hDX hside
  obtain ⟨yC, yD, hyC, hyD, hyCD⟩ :=
    hconnected C D X hCbranch hDbranch hCX hDX hside
  exact
    fkRectBlackBoundaryCyclePrimalComponent_dualEquiv_eq_of_rightBoundaryContacts_reachable
      R omega C D yC yD hyC hyD hyCD


theorem
    fkRectForcedDualSameSideOriginalComponent_of_rightBoundaryConnectivityReflection
    (R : FKRectTorus) (omega : R.Configuration)
    (hreflect :
      FKRectForcedDualSameSideRightBoundaryConnectivityReflection R omega) :
    FKRectForcedDualSameSideOriginalComponent R omega :=
  fkRectForcedDualSameSideOriginalComponent_of_rightBoundaryConnected
    R omega
      (fkRectForcedDualSameSideRightBoundaryConnected_of_reflection
        R omega hreflect)


theorem fkRectForcedDualSameSideOriginalComponent_of_sharedRightBoundaryContact
    (R : FKRectTorus) (omega : R.Configuration)
    (hcontact :
      FKRectForcedDualSameSideSharedRightBoundaryContact R omega) :
    FKRectForcedDualSameSideOriginalComponent R omega := by
  intro C D X hCbranch hDbranch hCX hDX hside
  obtain ⟨y, hyC, hyD⟩ :=
    hcontact C D X hCbranch hDbranch hCX hDX hside
  exact
    fkRectBlackBoundaryCyclePrimalComponent_dualEquiv_eq_of_sharedRightBoundaryContact
      R omega C D y hyC hyD

set_option maxHeartbeats 800000 in


theorem fkRectZeroTurnOriginalDualSameSideUnique_of_originalComponent
    (R : FKRectTorus) (omega : R.Configuration)
    (hcomponent : FKRectForcedDualSameSideOriginalComponent R omega) :
    FKRectZeroTurnOriginalDualSameSideUnique R omega := by
  classical
  intro C D X hCbranch hDbranch hCX hDX hside
  let eta := fkRectDualConfigurationEquiv R omega
  let bC := fkRectZeroTurnRemainderBlackDart R omega C
  let bD := fkRectZeroTurnRemainderBlackDart R omega D
  let cC : FKRectConfigurationBlackBoundaryCycle R omega := Quot.mk _ bC
  let cD : FKRectConfigurationBlackBoundaryCycle R omega := Quot.mk _ bD
  let dcC := fkRectBlackBoundaryCycleDualEquiv R omega cC
  let dcD := fkRectBlackBoundaryCycleDualEquiv R omega cD
  let x := fkRectMedialDartPrimalLabel R
    (fkRectDualBlackDartEquiv R omega bC).1
  have hcomp : fkRectBlackBoundaryCyclePrimalComponent R eta dcC =
      fkRectBlackBoundaryCyclePrimalComponent R eta dcD := by
    exact hcomponent C D X hCbranch hDbranch hCX hDX hside
  have hmemC : fkRectBlackBoundaryCycleInPrimalCluster R eta x dcC := by
    rw [fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent]
    simp [dcC, cC, x, fkRectBlackBoundaryCyclePrimalComponent]
  have hmemD : fkRectBlackBoundaryCycleInPrimalCluster R eta x dcD := by
    rw [fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent]
    exact hcomp.symm.trans
      ((fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent
        R eta x dcC).mp hmemC)
  have horigSign : 0 <
      (fkRectBlackBoundaryCycleWinding R omega cC).1 *
        (fkRectBlackBoundaryCycleWinding R omega cD).1 := by
    rw [show cC = Quot.mk _ bC from rfl,
      show cD = Quot.mk _ bD from rfl,
      fkRectBlackBoundaryCycleWinding_mk,
      fkRectBlackBoundaryCycleWinding_mk,
      ← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass R omega bC,
      ← fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass R omega bD]
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
  have hdualEq : dcC = dcD := by
    apply fkRectBlackBoundaryCycle_eq_of_card_nonzero_le_two_of_fst_mul_pos
      R eta x
      (card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_atVertex R eta x)
      hmemC hmemD hdualSign
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


theorem
    fkRectZeroTurnOriginalDualSameSideUnique_of_rightBoundaryConnectivityReflection
    (R : FKRectTorus) (omega : R.Configuration)
    (hreflect :
      FKRectForcedDualSameSideRightBoundaryConnectivityReflection R omega) :
    FKRectZeroTurnOriginalDualSameSideUnique R omega :=
  fkRectZeroTurnOriginalDualSameSideUnique_of_originalComponent R omega
    (fkRectForcedDualSameSideOriginalComponent_of_rightBoundaryConnectivityReflection
      R omega hreflect)


theorem fkRectPrimalBoundaryFiberSameSignUnique_unconditional
    (R : FKRectTorus) (omega : R.Configuration) :
    FKRectPrimalBoundaryFiberSameSignUnique R omega := by
  apply fkRectPrimalBoundaryFiberSameSignUnique_of_card_nonzero_le_two
  intro _ x
  exact card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_atVertex
    R omega x


end
end StatMech.FrontierD
