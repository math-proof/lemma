/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedExtremeClosed
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionCharge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryPotentialContradiction
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalBoundaryFiberWinding.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedIncidence.Part2
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

set_option maxHeartbeats 800000 in


theorem fkRectPrimalBoundaryFiberSameSignUnique_of_card_nonzero_le_two
    (R : FKRectTorus) (omega : R.Configuration)
    (hcard : ¬ FKRectHasNet R omega → ∀ x : R.Vertex,
      (fkRectPrimalClusterNonzeroBoundaryCycles R omega x).card ≤ 2) :
    FKRectPrimalBoundaryFiberSameSignUnique R omega := by
  classical
  intro hnoNet d e hcolor hfiber _hdVertical _heVertical hsign
  let pairing := fkRectConfigurationToMedialPairing R omega
  have blackCase (d0 e0 : FKMedialDart R.medialTorus)
      (bd be : FKMedialBlackDart R.medialTorus)
      (hbd : bd.1 = d0) (hbe : be.1 = e0)
      (hfiber0 : fkRectMedialComponentToPrimalComponent R omega
          ((fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk d0) =
        fkRectMedialComponentToPrimalComponent R omega
          ((fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk e0))
      (hsign0 : 0 < (fkRectWalkWinding R
            (fkRectMedialBoundaryPrimalOrbitWalk R omega d0)).1 *
          (fkRectWalkWinding R
            (fkRectMedialBoundaryPrimalOrbitWalk R omega e0)).1) :
      (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk d0 =
        (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk e0 := by
    let x := fkRectMedialDartPrimalLabel R d0
    have hreach : (fkRectOpenGraph R omega).Reachable x
        (fkRectMedialDartPrimalLabel R e0) := by
      apply SimpleGraph.ConnectedComponent.exact
      simpa [pairing] using hfiber0
    let C : FKRectConfigurationBlackBoundaryCycle R omega := Quot.mk _ bd
    let D : FKRectConfigurationBlackBoundaryCycle R omega := Quot.mk _ be
    have hC : fkRectBlackBoundaryCycleInPrimalCluster R omega x C := by
      rw [show C = Quot.mk _ bd from rfl,
        fkRectBlackBoundaryCycleInPrimalCluster_mk]
      simpa [x, hbd] using
        (SimpleGraph.Reachable.refl x :
          (fkRectOpenGraph R omega).Reachable x x)
    have hD : fkRectBlackBoundaryCycleInPrimalCluster R omega x D := by
      rw [show D = Quot.mk _ be from rfl,
        fkRectBlackBoundaryCycleInPrimalCluster_mk]
      simpa [hbe] using hreach
    let md := permOrbitVisitCount (fkMedialBoundaryStep pairing) bd.1 bd.1
    let me := permOrbitVisitCount (fkMedialBoundaryStep pairing) be.1 be.1
    have hmd : 0 < md := permOrbitVisitCount_self_pos _ _
    have hme : 0 < me := permOrbitVisitCount_self_pos _ _
    have hdscale := congrArg Prod.fst
      (fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_nsmul_blackCycle
        R omega bd)
    have hescale := congrArg Prod.fst
      (fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_nsmul_blackCycle
        R omega be)
    rw [fkRectBlackBoundaryPrimalCycleWalk_winding_eq_cycleClass] at hdscale hescale
    simp only [Prod.smul_fst, nsmul_eq_mul] at hdscale hescale
    have hsign' := hsign0
    rw [← hbd, ← hbe, hdscale, hescale] at hsign'
    have hmdInt : (0 : Int) < md := by exact_mod_cast hmd
    have hmeInt : (0 : Int) < me := by exact_mod_cast hme
    have hfactor : 0 < ((md : Int) * (me : Int)) *
        ((fkRectBlackBoundaryCycleClassWinding R pairing bd).1 *
          (fkRectBlackBoundaryCycleClassWinding R pairing be).1) := by
      rw [show ((md : Int) * (me : Int)) *
          ((fkRectBlackBoundaryCycleClassWinding R pairing bd).1 *
            (fkRectBlackBoundaryCycleClassWinding R pairing be).1) =
        ((md : Int) *
            (fkRectBlackBoundaryCycleClassWinding R pairing bd).1) *
          ((me : Int) *
            (fkRectBlackBoundaryCycleClassWinding R pairing be).1) by ring]
      simpa [md, me, pairing] using hsign'
    have hcycleSign : 0 <
        (fkRectBlackBoundaryCycleClassWinding R pairing bd).1 *
          (fkRectBlackBoundaryCycleClassWinding R pairing be).1 := by
      rcases (mul_pos_iff.mp hfactor) with hpos | hneg
      · exact hpos.2
      · exact absurd hneg.1 (not_lt_of_ge (mul_nonneg hmdInt.le hmeInt.le))
    have hCD : C = D := by
      apply fkRectBlackBoundaryCycle_eq_of_card_nonzero_le_two_of_fst_mul_pos
        R omega x (hcard hnoNet x) hC hD
      simpa [C, D, pairing] using hcycleSign
    have hsame : (fkMedialBlackBoundaryPerm pairing).SameCycle bd be := by
      exact Quotient.exact hCD
    apply SimpleGraph.ConnectedComponent.sound
    simpa [hbd, hbe] using
      (fkMedial_blackBoundary_sameCycle_iff_reachable pairing bd be).mp hsame
  cases hdcolor : fkMedialCheckerColor d
  · have hecolor : fkMedialCheckerColor e = false := by
      rw [← hcolor, hdcolor]
    exact blackCase d e ⟨d, hdcolor⟩ ⟨e, hecolor⟩ rfl rfl
      hfiber hsign
  · have hecolor : fkMedialCheckerColor e = true := by
      rw [← hcolor, hdcolor]
    let d' := fkMedialLocalMate pairing d
    let e' := fkMedialLocalMate pairing e
    have hd'black : fkMedialCheckerColor d' = false := by
      simp [d', fkMedialCheckerColor_localMate_eq_not, hdcolor]
    have he'black : fkMedialCheckerColor e' = false := by
      simp [e', fkMedialCheckerColor_localMate_eq_not, hecolor]
    have hdComponent :
        (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk d' =
          (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk d := by
      apply SimpleGraph.ConnectedComponent.sound
      exact (fkMedial_reachable_localMate pairing d).symm
    have heComponent :
        (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk e' =
          (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk e := by
      apply SimpleGraph.ConnectedComponent.sound
      exact (fkMedial_reachable_localMate pairing e).symm
    have hfiber' :
        fkRectMedialComponentToPrimalComponent R omega
            ((fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk d') =
          fkRectMedialComponentToPrimalComponent R omega
            ((fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk e') := by
      rw [hdComponent, heComponent]
      exact hfiber
    have hsign' : 0 < (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d')).1 *
        (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega e')).1 := by
      rw [show d' = fkMedialLocalMate pairing d from rfl,
        show e' = fkMedialLocalMate pairing e from rfl,
        fkRectMedialBoundaryPrimalOrbitWalk_winding_localMate,
        fkRectMedialBoundaryPrimalOrbitWalk_winding_localMate]
      simpa using hsign
    have hde' := blackCase d' e' ⟨d', hd'black⟩ ⟨e', he'black⟩
      rfl rfl hfiber' hsign'
    exact hdComponent.symm.trans (hde'.trans heComponent)


end
end StatMech.FrontierD
