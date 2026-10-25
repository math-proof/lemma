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
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part15


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hlhr_natAbs_cast (z : ℤ) : ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := by
  cases z with
  | ofNat n => simp
  | negSucc n =>
      rw [Int.natAbs_negSucc, Int.cast_negSucc, abs_neg,
        abs_of_nonneg (by positivity)]


theorem hlhr_intervalSpan_eq_latticeWidth (ts : List ℤ)
    (hlegal : (ofTurns 0 0 ts).LegalTurns) (p : ℕ × ℕ) :
    hlhr_intervalSpan (hlhr_height 0 ts) p =
      (Real.sqrt 3 / 2) * hlhr_latticeWidth ts p := by
  rw [hlhr_intervalSpan, hlhr_height_eq_latticeHeight ts hlegal p.2,
    hlhr_height_eq_latticeHeight ts hlegal p.1]
  have hs : 0 < Real.sqrt 3 / 2 := by positivity
  rw [show Real.sqrt 3 / 4 + Real.sqrt 3 / 2 * (hlhr_latticeHeight ts p.2 : ℝ) -
      (Real.sqrt 3 / 4 + Real.sqrt 3 / 2 * (hlhr_latticeHeight ts p.1 : ℝ)) =
      (Real.sqrt 3 / 2) * (hlhr_latticeDelta ts p : ℝ) by
    unfold hlhr_latticeDelta
    push_cast
    ring]
  rw [abs_mul, abs_of_pos hs]
  rw [← hlhr_natAbs_cast (hlhr_latticeDelta ts p)]
  rfl


theorem hlhr_latticeWidth_pos_of_span_pos (ts : List ℤ)
    (hlegal : (ofTurns 0 0 ts).LegalTurns) (p : ℕ × ℕ)
    (hspan : 0 < hlhr_intervalSpan (hlhr_height 0 ts) p) :
    0 < hlhr_latticeWidth ts p := by
  rw [hlhr_intervalSpan_eq_latticeWidth ts hlegal p] at hspan
  have hs : 0 < Real.sqrt 3 / 2 := by positivity
  have hw : (0 : ℝ) < (hlhr_latticeWidth ts p : ℝ) := by
    rcases mul_pos_iff.mp hspan with h | h
    · exact h.2
    · exact (not_lt_of_ge (le_of_lt hs) h.1).elim
  exact_mod_cast hw


theorem hlhr_latticeWidth_gt_of_span_gt (ts : List ℤ)
    (hlegal : (ofTurns 0 0 ts).LegalTurns) (p q : ℕ × ℕ)
    (hspan : hlhr_intervalSpan (hlhr_height 0 ts) p >
      hlhr_intervalSpan (hlhr_height 0 ts) q) :
    hlhr_latticeWidth ts p > hlhr_latticeWidth ts q := by
  rw [hlhr_intervalSpan_eq_latticeWidth ts hlegal p,
    hlhr_intervalSpan_eq_latticeWidth ts hlegal q] at hspan
  have hs : 0 < Real.sqrt 3 / 2 := by positivity
  have hw : (hlhr_latticeWidth ts q : ℝ) <
      (hlhr_latticeWidth ts p : ℝ) :=
    lt_of_mul_lt_mul_left hspan (le_of_lt hs)
  exact_mod_cast hw


end StatMech.Universality
