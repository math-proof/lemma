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
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part4


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


namespace HexHWContentDecomp

variable {D : Type}


theorem pair_injective (H : HexHWContentDecomp D) :
    Function.Injective H.pair := by
  intro d e hde
  apply H.turns_inj
  rw [H.reconstruct d, H.reconstruct e]
  exact congrArg (fun p : HexHWContentHalf × HexHWContentHalf =>
    hhc_halfTurns p.1 ++ hhc_halfTurns p.2) hde


theorem weight_factor (H : HexHWContentDecomp D) (x : ℝ) (d : D) :
    x ^ (H.turns d).length =
      hhc_halfWeight x (H.lower d) * hhc_halfWeight x (H.upper d) := by
  rw [H.reconstruct d, List.length_append, pow_add,
    hhc_halfWeight_eq_pow, hhc_halfWeight_eq_pow]

end HexHWContentDecomp
end StatMech.Universality
