/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeWeight.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part9


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


@[simp] theorem hhc_halfTurns_halfOfList (ts : List ℤ) :
    hhc_halfTurns (hhc_halfOfList ts) = ts := by
  classical
  unfold hhc_halfOfList
  split
  · next h => simp [hhc_halfTurns, h]
  · next h => simp [hhc_halfTurns, hhc_bridgeOfNonempty]


theorem hhc_halfOfList_strict (ts : List ℤ) :
    StrictDecreasingWidths (hhc_halfOfList ts).1 :=
  (hhc_halfOfList ts).2


theorem hhc_bridge_decomp_retains_turns (s : HexHWContentHalf) :
    (hexHW_bridge_decomp s : List (ℕ × ℤ)).map Prod.snd = hhc_halfTurns s := by
  rcases s with ⟨bs, hbs⟩
  simp only [hexHW_bridge_decomp_apply, bridgeRecompose, hhc_halfTurns,
    List.map_flatten]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro b _
  simp [HexBridge.rungs, Function.comp_def, List.map_map]


end StatMech.Universality
