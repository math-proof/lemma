/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part9


namespace StatMech.Universality

open HexWalk


theorem hlha_prefixAugment_eq_reverseAugment (ts : List ℤ) :
    hlha_prefixAugment ts =
      hlha_reverseAugment (ts.take (hexW2_cutPos 0 ts)) := by
  unfold hlha_prefixAugment hlha_prefixReverseData hlha_reverseAugment
  generalize hp : ts.take (hexW2_cutPos 0 ts) = pre
  cases pre with
  | nil => rfl
  | cons t us =>
      simp only
      unfold hlha_cutState
      rw [hp]

theorem hlha_normTurns_injective (d : HexReturnCoord) :
    Function.Injective (hlha_normTurns d) := by
  intro xs ys h
  unfold hlha_normTurns at h
  split at h
  · have := congrArg hsc_negTurns h
    simpa only [hsc_negTurns_negTurns] using this
  · exact h

theorem hlha_augmentSide_injective_fixed (d : HexReturnCoord) :
    Function.Injective (hlha_augmentSide d) := by
  intro xs ys h
  apply hlha_normTurns_injective d
  have := congrArg (List.drop 2) h
  simpa [hlha_augmentSide] using this

theorem hlha_loopReverse_injective : Function.Injective loopReverse := by
  intro xs ys h
  have := congrArg loopReverse h
  simpa only [loopReverse_involutive] using this

theorem hlha_reverseDir_mod_cases (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (haway : HLHAAwayDir (hlha_negCoord
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir)) :
    (hlha_negCoord
          (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨1, 1⟩ ∧
        (6 : ℤ) ∣ ts.sum - (-2)) ∨
      (hlha_negCoord
          (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨0, 1⟩ ∧
        (6 : ℤ) ∣ ts.sum - (-1)) ∨
      (hlha_negCoord
          (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨-1, 0⟩ ∧
        (6 : ℤ) ∣ ts.sum) ∨
      (hlha_negCoord
          (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ts).dir = ⟨-1, -1⟩ ∧
        (6 : ℤ) ∣ ts.sum - 1) := by
  rcases haway with h | h | h | h
  · exact Or.inl ⟨h, hlha_reverseDir_mod_h1 ts hlegal h⟩
  · exact Or.inr (Or.inl ⟨h, hlha_reverseDir_mod_h2 ts hlegal h⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨h, hlha_reverseDir_mod_h3 ts hlegal h⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨h, hlha_reverseDir_mod_h4 ts hlegal h⟩))

theorem hlha_negTurns_sum (ts : List ℤ) :
    (hsc_negTurns ts).sum = -ts.sum := by
  induction ts with
  | nil => simp [hsc_negTurns]
  | cons t ts ih =>
      unfold hsc_negTurns at ih ⊢
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

theorem hlha_cross_h1_h4_sum {xs ys : List ℤ}
    (h : hlha_augmentSide ⟨1, 1⟩ (loopReverse xs) =
      hlha_augmentSide ⟨-1, -1⟩ (loopReverse ys)) :
    xs.sum = -ys.sum := by
  have hs := congrArg List.sum h
  simp [hlha_augmentSide, hlha_normTurns, hlha_useSwap,
    hlha_cutTurn, loopReverse_sum, hlha_negTurns_sum] at hs
  omega

theorem hlha_cross_h4_h1_sum {xs ys : List ℤ}
    (h : hlha_augmentSide ⟨-1, -1⟩ (loopReverse xs) =
      hlha_augmentSide ⟨1, 1⟩ (loopReverse ys)) :
    xs.sum = -ys.sum := by
  have hs := hlha_cross_h1_h4_sum h.symm
  omega

theorem hlha_cross_h2_h3_sum {xs ys : List ℤ}
    (h : hlha_augmentSide ⟨0, 1⟩ (loopReverse xs) =
      hlha_augmentSide ⟨-1, 0⟩ (loopReverse ys)) :
    xs.sum = -ys.sum := by
  have hs := congrArg List.sum h
  simp [hlha_augmentSide, hlha_normTurns, hlha_useSwap,
    hlha_cutTurn, loopReverse_sum, hlha_negTurns_sum] at hs
  omega

theorem hlha_cross_h3_h2_sum {xs ys : List ℤ}
    (h : hlha_augmentSide ⟨-1, 0⟩ (loopReverse xs) =
      hlha_augmentSide ⟨0, 1⟩ (loopReverse ys)) :
    xs.sum = -ys.sum := by
  have hs := hlha_cross_h2_h3_sum h.symm
  omega


theorem hlha_reverseAugment_injective_of_away {xs ys : List ℤ}
    (hxlegal : ∀ t ∈ xs, t = 1 ∨ t = -1)
    (hylegal : ∀ t ∈ ys, t = 1 ∨ t = -1)
    (hxaway : xs ≠ [] → HLHAAwayDir (hlha_negCoord
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base xs).dir))
    (hyaway : ys ≠ [] → HLHAAwayDir (hlha_negCoord
      (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base ys).dir))
    (heq : hlha_reverseAugment xs = hlha_reverseAugment ys) :
    xs = ys := by
  cases xs with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          have hlen := congrArg List.length heq
          simp [hlha_reverseAugment, hlha_emptyAugment,
            hlha_augmentSide_length] at hlen
  | cons x xs =>
      cases ys with
      | nil =>
          have hlen := congrArg List.length heq
          simp [hlha_reverseAugment, hlha_emptyAugment,
            hlha_augmentSide_length] at hlen
      | cons y ys =>
          have hx := hxlegal x (by simp)
          have hy := hylegal y (by simp)
          have hxcase := hlha_reverseDir_mod_cases (x :: xs) hxlegal
            (hxaway (by simp))
          have hycase := hlha_reverseDir_mod_cases (y :: ys) hylegal
            (hyaway (by simp))
          change hlha_augmentSide (hlha_negCoord
              (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base (x :: xs)).dir)
                (loopReverse xs) =
            hlha_augmentSide (hlha_negCoord
              (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base (y :: ys)).dir)
                (loopReverse ys) at heq
          rcases hxcase with ⟨hxd, hxm⟩ | ⟨hxd, hxm⟩ |
              ⟨hxd, hxm⟩ | ⟨hxd, hxm⟩ <;>
            rcases hycase with ⟨hyd, hym⟩ | ⟨hyd, hym⟩ |
              ⟨hyd, hym⟩ | ⟨hyd, hym⟩
          all_goals rw [hxd, hyd] at heq
          all_goals obtain ⟨kx, hkx⟩ := hxm
          all_goals obtain ⟨ky, hky⟩ := hym
          all_goals simp only [List.sum_cons] at hkx hky
          · have hi := hlha_augmentSide_injective_fixed ⟨1, 1⟩ heq
            have htail := hlha_loopReverse_injective hi
            subst ys
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
              simp_all <;> omega
          · simp [hlha_augmentSide, hlha_cutTurn] at heq
          · simp [hlha_augmentSide, hlha_cutTurn] at heq
          · have hsum := hlha_cross_h1_h4_sum heq
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> omega
          · simp [hlha_augmentSide, hlha_cutTurn] at heq
          · have hi := hlha_augmentSide_injective_fixed ⟨0, 1⟩ heq
            have htail := hlha_loopReverse_injective hi
            subst ys
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
              simp_all <;> omega
          · have hsum := hlha_cross_h2_h3_sum heq
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> omega
          · simp [hlha_augmentSide, hlha_cutTurn] at heq
          · simp [hlha_augmentSide, hlha_cutTurn] at heq
          · have hsum := hlha_cross_h3_h2_sum heq
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> omega
          · have hi := hlha_augmentSide_injective_fixed ⟨-1, 0⟩ heq
            have htail := hlha_loopReverse_injective hi
            subst ys
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
              simp_all <;> omega
          · simp [hlha_augmentSide, hlha_cutTurn] at heq
          · have hsum := hlha_cross_h4_h1_sum heq
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> omega
          · simp [hlha_augmentSide, hlha_cutTurn] at heq
          · simp [hlha_augmentSide, hlha_cutTurn] at heq
          · have hi := hlha_augmentSide_injective_fixed ⟨-1, -1⟩ heq
            have htail := hlha_loopReverse_injective hi
            subst ys
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
              simp_all <;> omega


end StatMech.Universality
