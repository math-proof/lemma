/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Summable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4
import Def.StatisticalMechanics.Code.Universality.HexW2Summable


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


theorem hexW2S_bridgeWt_nonneg {x : ℝ} (hx : 0 ≤ x) (b : HexW2SBridge) :
    0 ≤ hexW2S_bridgeWt x b :=
  hexSAWwt_nonneg 0 b.head hx b.turns


theorem hexW2S_bridgeWt_eq_halfWt (x : ℝ) (mid : ℂ) (head : ℤ) (turns : List ℤ) :
    hexW2S_bridgeWt x ⟨head, turns⟩ = hexW2_halfWt x ⟨mid, head, turns⟩ := by
  change hexSAWwt 0 head x turns = hexSAWwt mid head x turns
  exact hexW2S_hexSAWwt_mid_indep mid 0 head x turns


theorem hexW2S_bridge_summable {x χ : ℝ} (hx : 0 ≤ x) (hxχ : x ≤ χ)
    (bridgeMem : ℤ × List ℤ → Prop)
    (hBcrit : Summable (fun b : {b // bridgeMem b} => hexSAWwt 0 b.1.1 χ b.1.2)) :
    Summable (fun b : {b // bridgeMem b} => hexW2S_bridgeWt x ⟨b.1.1, b.1.2⟩) :=
  hBcrit.of_nonneg_of_le (fun b => hexSAWwt_nonneg 0 b.1.1 hx b.1.2)
    (fun b => hexW2S_hexSAWwt_mono_fugacity 0 b.1.1 hx hxχ b.1.2)


end StatMech.Universality
