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
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part6


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hlhr_intervalSpan_eq_oriented (f : ℕ → ℝ) (up : Bool) {lo hi : ℕ}
    (hlt : lo < hi) (hahead : HLHRAhead f up lo hi) :
    hlhr_intervalSpan f (lo, hlhr_lastExtremum f up lo hi) =
      hlhr_orientedSpan f up lo (hlhr_lastExtremum f up lo hi) := by
  have hpos := hlhr_orientedSpan_pos f up hlt hahead
  cases up with
  | false =>
      simp only [hlhr_intervalSpan, hlhr_orientedSpan, hlhr_signed,
        Bool.false_eq_true, ↓reduceIte] at hpos ⊢
      rw [abs_of_neg (by linarith)]
      ring
  | true =>
      simp only [hlhr_intervalSpan, hlhr_orientedSpan, hlhr_signed,
        ↓reduceIte] at hpos ⊢
      exact abs_of_pos hpos


theorem hlhr_intervalSpans_ordered (f : ℕ → ℝ) (hi fuel lo : ℕ) (up : Bool)
    (hlt : lo < hi) (hahead : HLHRAhead f up lo hi) :
    let ws := hlhr_intervalSpans f (hlhr_intervalsAux f hi fuel up lo)
    ws.Pairwise (· > ·) ∧
      (∀ w ∈ ws, 0 < w) ∧
      (∀ w ∈ ws,
        w ≤ hlhr_orientedSpan f up lo (hlhr_lastExtremum f up lo hi)) := by
  induction fuel generalizing up lo with
  | zero =>
      simp [hlhr_intervalsAux, hlhr_intervalSpans]
  | succ fuel ih =>
      let k := hlhr_lastExtremum f up lo hi
      have hklo : lo < k := by
        dsimp [k]
        exact hlhr_lastExtremum_gt f up hlt hahead
      have hkhi : k ≤ hi := by
        dsimp [k]
        exact hlhr_lastExtremum_le_hi f up (le_of_lt hlt)
      have hfirst : hlhr_intervalSpan f (lo, k) =
          hlhr_orientedSpan f up lo k := by
        dsimp [k]
        exact hlhr_intervalSpan_eq_oriented f up hlt hahead
      have hfirstPos : 0 < hlhr_intervalSpan f (lo, k) := by
        rw [hfirst]
        dsimp [k]
        exact hlhr_orientedSpan_pos f up hlt hahead
      simp only [hlhr_intervalsAux, hlt, ↓reduceIte, hlhr_intervalSpans,
        List.map_cons]
      let tail := hlhr_intervalSpans f
        (hlhr_intervalsAux f hi fuel (!up) k)
      change
        (hlhr_intervalSpan f (lo, k) :: tail).Pairwise (· > ·) ∧
          (∀ w ∈ hlhr_intervalSpan f (lo, k) :: tail, 0 < w) ∧
          (∀ w ∈ hlhr_intervalSpan f (lo, k) :: tail,
            w ≤ hlhr_orientedSpan f up lo k)
      by_cases hk : k < hi
      · have hnext : HLHRAhead f (!up) k hi := by
          dsimp [k]
          exact hlhr_ahead_next f up hlt
        have htail := ih k (!up) hk hnext
        have hnextLt :
            hlhr_orientedSpan f (!up) k
                (hlhr_lastExtremum f (!up) k hi) <
              hlhr_intervalSpan f (lo, k) := by
          rw [hfirst]
          dsimp [k]
          exact hlhr_orientedSpan_next_lt f up hlt hahead hk
        rcases htail with ⟨htailPair, htailPos, htailBound⟩
        refine ⟨List.pairwise_cons.mpr ⟨?_, htailPair⟩, ?_, ?_⟩
        · intro w hw
          exact lt_of_le_of_lt (htailBound w hw) hnextLt
        · intro w hw
          simp only [List.mem_cons] at hw
          rcases hw with rfl | hw
          · exact hfirstPos
          · exact htailPos w hw
        · intro w hw
          simp only [List.mem_cons] at hw
          rcases hw with rfl | hw
          · exact le_of_eq hfirst
          · exact le_trans (htailBound w hw)
              (le_trans (le_of_lt hnextLt) (le_of_eq hfirst))
      · have hkeq : k = hi := by omega
        have htailNil : hlhr_intervalsAux f hi fuel (!up) hi = [] := by
          cases fuel <;> simp [hlhr_intervalsAux]
        have htail : tail = [] := by
          simp [tail, hkeq, htailNil, hlhr_intervalSpans]
        rw [htail]
        simp only [List.pairwise_singleton, List.mem_singleton, forall_eq]
        exact ⟨trivial, hfirstPos, le_of_eq hfirst⟩


end StatMech.Universality
