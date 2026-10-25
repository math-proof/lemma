/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedOpenBoundaryDependence
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedAnchor
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectZeroTurnRemainderOrientedDart_checkerColor
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (color : Bool) :
    fkMedialCheckerColor
        (fkRectZeroTurnRemainderOrientedDart R omega C color) = color := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let b := fkRectZeroTurnRemainderBlackDart R omega C
  cases color
  · exact b.2
  · change fkMedialCheckerColor (fkMedialLocalMate pairing b.1) = true
    rw [fkMedialCheckerColor_localMate_eq_not, b.2]
    rfl


theorem fkRectZeroTurnRemainderOrientedDart_component
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (color : Bool) :
    (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
        (fkRectZeroTurnRemainderOrientedDart R omega C color) = C.1 := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let b := fkRectZeroTurnRemainderBlackDart R omega C
  cases color
  · exact fkRectZeroTurnRemainderBlackDart_component R omega C
  · calc
      (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk
          (fkMedialLocalMate pairing b.1) =
          (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk
            b.1 := by
        apply SimpleGraph.ConnectedComponent.sound
        exact (fkMedial_reachable_localMate pairing b.1).symm
      _ = C.1 := fkRectZeroTurnRemainderBlackDart_component R omega C


theorem fkRectZeroTurnRemainderOrientedDart_winding_fst_pos_iff
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (color : Bool) :
    0 < (fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R omega
        (fkRectZeroTurnRemainderOrientedDart R omega C color))).1 ↔
      fkRectZeroTurnRemainderSide R omega C = !color := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let b := fkRectZeroTurnRemainderBlackDart R omega C
  let m := permOrbitVisitCount (fkMedialBoundaryStep pairing) b.1 b.1
  let w := fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega b)
  have hmNat : 0 < m := permOrbitVisitCount_self_pos _ _
  have hm : (0 : Int) < m := by exact_mod_cast hmNat
  have horbit : fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R omega b.1) = m • w := by
    exact fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_nsmul_blackCycle
      R omega b
  cases color
  · change 0 < (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega b.1)).1 ↔
        fkRectZeroTurnRemainderSide R omega C = true
    rw [horbit]
    simp only [nsmul_eq_mul]
    rw [fkRectZeroTurnRemainderSide_eq_true_iff]
    change 0 < (m : Int) * w.1 ↔ 0 < w.1
    constructor <;> intro h <;> nlinarith
  · change 0 < (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega
          (fkMedialLocalMate pairing b.1))).1 ↔
        fkRectZeroTurnRemainderSide R omega C = false
    rw [fkRectMedialBoundaryPrimalOrbitWalk_winding_localMate, horbit]
    simp only [Prod.fst_neg, nsmul_eq_mul]
    rw [fkRectZeroTurnRemainderSide_eq_false_iff]
    change 0 < -((m : Int) * w.1) ↔ w.1 < 0
    constructor <;> intro h <;> nlinarith


theorem fkRectZeroTurnRemainderOrientedDart_winding_fst_neg_iff
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (color : Bool) :
    (fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R omega
        (fkRectZeroTurnRemainderOrientedDart R omega C color))).1 < 0 ↔
      fkRectZeroTurnRemainderSide R omega C = color := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let b := fkRectZeroTurnRemainderBlackDart R omega C
  let m := permOrbitVisitCount (fkMedialBoundaryStep pairing) b.1 b.1
  let w := fkRectWalkWinding R
    (fkRectBlackBoundaryPrimalCycleWalk R omega b)
  have hmNat : 0 < m := permOrbitVisitCount_self_pos _ _
  have hm : (0 : Int) < m := by exact_mod_cast hmNat
  have horbit : fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R omega b.1) = m • w := by
    exact fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_nsmul_blackCycle
      R omega b
  cases color
  · change (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega b.1)).1 < 0 ↔
        fkRectZeroTurnRemainderSide R omega C = false
    rw [horbit]
    simp only [nsmul_eq_mul]
    rw [fkRectZeroTurnRemainderSide_eq_false_iff]
    change (m : Int) * w.1 < 0 ↔ w.1 < 0
    constructor <;> intro h <;> nlinarith
  · change (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega
          (fkMedialLocalMate pairing b.1))).1 < 0 ↔
        fkRectZeroTurnRemainderSide R omega C = true
    rw [fkRectMedialBoundaryPrimalOrbitWalk_winding_localMate, horbit]
    simp only [Prod.fst_neg, nsmul_eq_mul]
    rw [fkRectZeroTurnRemainderSide_eq_true_iff]
    change -((m : Int) * w.1) < 0 ↔ 0 < w.1
    constructor <;> intro h <;> nlinarith


end
end StatMech.FrontierD
