/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotRoute.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialUnitWindingSplitHall
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMedialCutAlignment.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLayeredCutBalance
import Def.StatisticalMechanics.Code.FrontierD.SixVertexTransitionRetieExact
open Equiv


namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}

theorem fkMedialLayeredTwoCutBalanced_of_balance
    (source : Bool -> FKMedialLoopPairing T)
    (first second : T.Vertex)
    (hbalance : FKMedialLayeredTwoCutBalance source first second) :
    FKMedialLayeredTwoCutBalanced source first second := by
  classical
  rcases hbalance with ⟨hfirst, hsecond⟩
  unfold FKMedialLayeredTwoCutBalanced FKMedialTwoCutSplitScore
  by_cases hff : FKMedialCutSplits (source false) first <;>
    by_cases hfs : FKMedialCutSplits
      (fkMedialTogglePairingAt (source false) first) second <;>
    simp_all


theorem intCast_fkMedialLoopCount_twoToggle_sub_eq_splitScore
    (pairing : FKMedialLoopPairing T) (first second : T.Vertex) :
    (fkMedialLoopCount T
        (fkMedialTogglePairingAt
          (fkMedialTogglePairingAt pairing first) second) : Int) -
      fkMedialLoopCount T pairing =
        FKMedialTwoCutSplitScore pairing first second := by
  classical
  by_cases hfirst : FKMedialCutSplits pairing first <;>
    by_cases hsecond : FKMedialCutSplits
      (fkMedialTogglePairingAt pairing first) second
  · have hfirstCount := fkMedialLoopCount_toggle_of_reachable
      T pairing first hfirst
    have hsecondCount := fkMedialLoopCount_toggle_of_reachable T
      (fkMedialTogglePairingAt pairing first) second hsecond
    simp [FKMedialTwoCutSplitScore, hfirst, hsecond]
    omega
  · have hfirstCount := fkMedialLoopCount_toggle_of_reachable
      T pairing first hfirst
    have hsecondCount := fkMedialLoopCount_toggle_of_not_reachable T
      (fkMedialTogglePairingAt pairing first) second hsecond
    simp [FKMedialTwoCutSplitScore, hfirst, hsecond]
    omega
  · have hfirstCount := fkMedialLoopCount_toggle_of_not_reachable
      T pairing first hfirst
    have hsecondCount := fkMedialLoopCount_toggle_of_reachable T
      (fkMedialTogglePairingAt pairing first) second hsecond
    simp [FKMedialTwoCutSplitScore, hfirst, hsecond]
    omega
  · have hfirstCount := fkMedialLoopCount_toggle_of_not_reachable
      T pairing first hfirst
    have hsecondCount := fkMedialLoopCount_toggle_of_not_reachable T
      (fkMedialTogglePairingAt pairing first) second hsecond
    simp [FKMedialTwoCutSplitScore, hfirst, hsecond]
    omega


theorem fkMedialLayeredTwoCutBalanced_iff_loopCount_eq
    (source : Bool -> FKMedialLoopPairing T)
    (first second : T.Vertex) :
    FKMedialLayeredTwoCutBalanced source first second <->
      fkMedialLoopCount T
          (fkMedialTogglePairingAt
            (fkMedialTogglePairingAt (source false) first) second) +
        fkMedialLoopCount T
          (fkMedialTogglePairingAt
            (fkMedialTogglePairingAt (source true) first) second) =
        fkMedialLoopCount T (source false) +
          fkMedialLoopCount T (source true) := by
  have hfalse := intCast_fkMedialLoopCount_twoToggle_sub_eq_splitScore
    (source false) first second
  have htrue := intCast_fkMedialLoopCount_twoToggle_sub_eq_splitScore
    (source true) first second
  unfold FKMedialLayeredTwoCutBalanced
  constructor <;> intro h <;> omega


end
end StatMech.FrontierD
