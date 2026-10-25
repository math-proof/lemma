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
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part3


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hhc_halfWeight_eq_pow (x : ℝ) (s : HexHWContentHalf) :
    hhc_halfWeight x s = x ^ (hhc_halfTurns s).length := by
  rcases s with ⟨bs, hbs⟩
  induction bs with
  | nil => simp [hhc_halfWeight, hhc_halfTurns]
  | cons b bs ih =>
      let tail : HexHWContentHalf := ⟨bs, (strictDecreasingWidths_cons.mp hbs).2⟩
      have hi := ih (hbs := (strictDecreasingWidths_cons.mp hbs).2)
      simp only [hhc_halfWeight, hhc_halfTurns, List.map_cons, List.flatten_cons,
        List.prod_cons, hhc_bridgeWeight, List.length_append, pow_add]
      simpa [hhc_halfWeight, hhc_halfTurns, tail] using
        congrArg (fun z => x ^ b.content.length * z) hi


theorem hhc_halfWeight_nonneg {x : ℝ} (hx : 0 ≤ x) (s : HexHWContentHalf) :
    0 ≤ hhc_halfWeight x s := by
  rw [hhc_halfWeight_eq_pow]
  positivity


end StatMech.Universality
