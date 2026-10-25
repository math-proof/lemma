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
import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part2


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hlhr_singleLeft_legal :
    (ofTurns 0 0 [(1 : ℤ)]).IsLegalSAW := by
  have hr := hexW1Exit_singleRight_legal (0 : ℂ) 0
  refine ⟨?_, ?_⟩
  · simpa [hsc_negTurns] using
      hsc_genLegalTurns 0 0 [(-1 : ℤ)] hr.1
  · simpa [hsc_negTurns] using
      hsc_genIsSAW 0 0 [(-1 : ℤ)] hr.2


theorem hlhr_singleLeft_not_halfSpace :
    ¬ HLHRLiteralHalfSpace 0 [(1 : ℤ)] := by
  intro h
  have hk := h 1 (by omega) (by simp)
  have hone : (halfStep 1).re = 0 := by
    rw [hexWall3_halfStep_re]
    rw [show Real.pi / 6 + ((1 : ℤ) : ℝ) * (Real.pi / 3) =
        Real.pi / 2 by push_cast; ring,
      Real.cos_pi_div_two]
    ring
  norm_num [hlhr_height, hexW2_partialDisp, hexInfra_stepReSum,
    hexInfra_headAccum, hlhr_halfStep_zero_re, hone] at hk

theorem hlhr_append_eq_singleLeft (lower upper : List ℤ)
    (h : [(1 : ℤ)] = lower ++ upper) :
    lower = [] ∧ upper = [1] ∨ lower = [1] ∧ upper = [] := by
  have hlen := congrArg List.length h
  simp only [List.length_singleton, List.length_append] at hlen
  cases lower with
  | nil =>
      left
      simp_all
  | cons l lower =>
      right
      simp only [List.length_cons] at hlen
      have hu : upper = [] := List.length_eq_zero_iff.mp (by omega)
      subst upper
      simp only [List.append_nil] at h
      exact ⟨h.symm, rfl⟩


theorem hlhr_no_unaugmented_split_singleLeft :
    ¬ ∃ lower upper : List ℤ,
      [(1 : ℤ)] = lower ++ upper ∧
      HLHRLiteralHalfSpace 0 lower ∧
        HLHRLiteralHalfSpace 0 upper := by
  rintro ⟨lower, upper, hrec, hlo, hup⟩
  rcases hlhr_append_eq_singleLeft lower upper hrec with h | h
  · exact hlhr_singleLeft_not_halfSpace (h.2 ▸ hup)
  · exact hlhr_singleLeft_not_halfSpace (h.1 ▸ hlo)


end StatMech.Universality
