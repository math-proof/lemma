/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Summable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4
import Def.StatisticalMechanics.Code.Universality.HexW2Summable.Part2


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


theorem hexW2S_diff_summable_of_finite (a : ℂ) (h0 : ℤ) {x χ : ℝ} (hx : 0 ≤ x)
    (hxχ : x ≤ χ) (memD : List ℤ → Prop) [Finite {ts // memD ts}] :
    Summable (fun d : {ts // memD ts} => hexSAWwt a h0 x d.1) :=
  hexW2S_diff_summable a h0 hx hxχ memD Summable.of_finite


theorem hexW2S_bridge_summable_of_finite {x χ : ℝ} (hx : 0 ≤ x) (hxχ : x ≤ χ)
    (bridgeMem : ℤ × List ℤ → Prop) [Finite {b // bridgeMem b}] :
    Summable (fun b : {b // bridgeMem b} => hexW2S_bridgeWt x ⟨b.1.1, b.1.2⟩) :=
  hexW2S_bridge_summable hx hxχ bridgeMem Summable.of_finite

end StatMech.Universality
