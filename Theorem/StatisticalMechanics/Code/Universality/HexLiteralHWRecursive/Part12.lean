/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexW2Summable.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part12


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hlhr_intervalWeight_eq_pow_turns (x : ℝ) (ts : List ℤ)
    (ps : List (ℕ × ℕ)) :
    (ps.map (hlhr_intervalWeight x ts)).prod =
      x ^ (hlhr_intervalTurns ts ps).length := by
  induction ps with
  | nil => simp [hlhr_intervalTurns]
  | cons p ps ih =>
      simp only [hlhr_intervalWeight, hlhr_intervalTurns, List.map_cons,
        List.prod_cons, List.flatten_cons, List.length_append, pow_add]
      rw [ih]
      rfl


theorem hlhr_literalInterval_weight_factor (h0 : ℤ) (ts : List ℤ)
    (hhalf : HLHRLiteralHalfSpace h0 ts) (x : ℝ) :
    ((hlhr_literalIntervals h0 ts).map (hlhr_intervalWeight x ts)).prod =
      x ^ ts.length := by
  rw [hlhr_intervalWeight_eq_pow_turns,
    hlhr_literalIntervals_reconstruct h0 ts hhalf]


end StatMech.Universality
