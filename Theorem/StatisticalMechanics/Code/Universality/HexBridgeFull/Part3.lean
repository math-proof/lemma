/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
import Def.StatisticalMechanics.Code.Universality.HexBridgeFull.Part3


namespace StatMech.Universality

open List

open HexWalk


@[simp]
theorem hxb_walkOfBridges_startMid (a : ℂ) (h0 : ℤ) (bs : List HexBridge) :
    (hxb_walkOfBridges a h0 bs).startMid = a := rfl

@[simp]
theorem hxb_walkOfBridges_h0 (a : ℂ) (h0 : ℤ) (bs : List HexBridge) :
    (hxb_walkOfBridges a h0 bs).h0 = h0 := rfl


theorem hxb_walkOfBridges_turns (a : ℂ) (h0 : ℤ) (bs : List HexBridge) :
    (hxb_walkOfBridges a h0 bs).turns = (bs.map HexBridge.content).flatten := by
  unfold hxb_walkOfBridges hxb_walkOf hxb_rungTurns bridgeRecompose
  simp only [ofTurns_turns]
  rw [List.map_flatten, List.map_map]
  congr 1
  apply List.map_congr_left
  intro b _
  simp [HexBridge.rungs, List.map_map]


@[simp]
theorem hxb_walkOfBridges_nil (a : ℂ) (h0 : ℤ) :
    hxb_walkOfBridges a h0 [] = trivialWalk a h0 := by
  unfold hxb_walkOfBridges hxb_walkOf hxb_rungTurns
  simp [bridgeRecompose, trivialWalk, ofTurns]


@[simp]
theorem hxb_walkOfBridges_numVertices (a : ℂ) (h0 : ℤ) (bs : List HexBridge) :
    (hxb_walkOfBridges a h0 bs).numVertices = (bridgeRecompose bs).length + 1 := by
  rw [hxb_walkOfBridges, hxb_walkOf_numVertices]


theorem hxb_walkOfBridges_turning_cons (a : ℂ) (h0 : ℤ) (b : HexBridge) (bs : List HexBridge) :
    (hxb_walkOfBridges a h0 (b :: bs)).turning
      = (Real.pi / 3) * ((b.content).sum : ℝ)
        + (hxb_walkOfBridges a h0 bs).turning := by
  simp only [hxb_walkOfBridges, hxb_walkOf, hxb_rungTurns, turning, turnCount, ofTurns_turns,
    bridgeRecompose_cons, List.map_append, List.sum_append]
  have hb : (b.rungs.map Prod.snd).sum = b.content.sum := by
    simp [HexBridge.rungs, List.map_map]
  rw [hb]
  push_cast
  ring


end StatMech.Universality
