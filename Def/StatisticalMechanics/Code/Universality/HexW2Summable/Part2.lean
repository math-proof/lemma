/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Summable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexW2Summable.Part2


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


noncomputable def hexW2S_highestCut_summClosed (a : ℂ) (h0 : ℤ) {x χ : ℝ} (hx : 0 < x)
    (hxle : x ≤ χ)
    (memD : List ℤ → Prop)
    (bridgeMem : ℤ × List ℤ → Prop)
    (split : {ts // memD ts} → {b : ℤ × List ℤ // bridgeMem b} × {b : ℤ × List ℤ // bridgeMem b})
    (hwtB1 : ∀ d, hexW2S_bridgeWt x ⟨(split d).1.1.1, (split d).1.1.2⟩
        = hexSAWwt a h0 x (d.1.take (hexW2_cutPos h0 d.1)))
    (hwtB2 : ∀ d, hexW2S_bridgeWt x ⟨(split d).2.1.1, (split d).2.1.2⟩
        = hexSAWwt (hexDropMid a h0 d.1 (hexW2_cutPos h0 d.1))
            (h0 + (d.1.take (hexW2_cutPos h0 d.1)).sum) x (d.1.drop (hexW2_cutPos h0 d.1)))
    (split_inj : Function.Injective split)
    (hDcrit : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 χ d.1))
    (hBcrit : Summable (fun b : {b : ℤ × List ℤ // bridgeMem b} => hexSAWwt 0 b.1.1 χ b.1.2)) :
    HexHighestCut x⁻¹ :=
  hexW2_highestCut a h0 hx memD
    ({b : ℤ × List ℤ // bridgeMem b})
    (fun b => hexW2S_bridgeWt x ⟨b.1.1, b.1.2⟩)
    (fun b => hexW2S_bridgeWt_nonneg (le_of_lt hx) ⟨b.1.1, b.1.2⟩)
    split hwtB1 hwtB2 split_inj
    (hexW2S_diff_summable a h0 (le_of_lt hx) hxle memD hDcrit)
    (hexW2S_bridge_summable (le_of_lt hx) hxle bridgeMem hBcrit)


noncomputable def hexW2S_highestCut_summClosed_chi (a : ℂ) (h0 : ℤ)
    (memD : List ℤ → Prop)
    (bridgeMem : ℤ × List ℤ → Prop)
    (split : {ts // memD ts} → {b : ℤ × List ℤ // bridgeMem b} × {b : ℤ × List ℤ // bridgeMem b})
    (hwtB1 : ∀ d, hexW2S_bridgeWt hexChiE ⟨(split d).1.1.1, (split d).1.1.2⟩
        = hexSAWwt a h0 hexChiE (d.1.take (hexW2_cutPos h0 d.1)))
    (hwtB2 : ∀ d, hexW2S_bridgeWt hexChiE ⟨(split d).2.1.1, (split d).2.1.2⟩
        = hexSAWwt (hexDropMid a h0 d.1 (hexW2_cutPos h0 d.1))
            (h0 + (d.1.take (hexW2_cutPos h0 d.1)).sum) hexChiE (d.1.drop (hexW2_cutPos h0 d.1)))
    (split_inj : Function.Injective split)
    (hDcrit : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
    (hBcrit : Summable (fun b : {b : ℤ × List ℤ // bridgeMem b} =>
      hexSAWwt 0 b.1.1 hexChiE b.1.2)) :
    HexHighestCut hexChiE⁻¹ :=
  hexW2S_highestCut_summClosed a h0 hexChiE_pos (le_refl hexChiE) memD bridgeMem split
    hwtB1 hwtB2 split_inj hDcrit hBcrit


end StatMech.Universality
