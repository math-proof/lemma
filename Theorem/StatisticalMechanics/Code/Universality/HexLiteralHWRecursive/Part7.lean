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
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part7


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hlhr_intervalsAux_reconstruct (f : ℕ → ℝ) (root : List ℤ)
    (fuel lo : ℕ) (up : Bool) (hlo : lo ≤ root.length)
    (hfuel : root.length - lo ≤ fuel)
    (hahead : lo < root.length → HLHRAhead f up lo root.length) :
    hlhr_intervalTurns root
        (hlhr_intervalsAux f root.length fuel up lo) = root.drop lo := by
  induction fuel generalizing up lo with
  | zero =>
      have heq : lo = root.length := by omega
      subst lo
      simp [hlhr_intervalsAux, hlhr_intervalTurns]
  | succ fuel ih =>
      by_cases hlt : lo < root.length
      · let k := hlhr_lastExtremum f up lo root.length
        have ha := hahead hlt
        have hklo : lo < k := by
          dsimp [k]
          exact hlhr_lastExtremum_gt f up hlt ha
        have hkhi : k ≤ root.length := by
          dsimp [k]
          exact hlhr_lastExtremum_le_hi f up (le_of_lt hlt)
        have hfuel' : root.length - k ≤ fuel := by omega
        have hnext : HLHRAhead f (!up) k root.length := by
          dsimp [k]
          exact hlhr_ahead_next f up hlt
        have hrec := ih k (!up) hkhi hfuel' (fun _ => hnext)
        simp only [hlhr_intervalsAux, hlt, ↓reduceIte, hlhr_intervalTurns,
          List.map_cons, List.flatten_cons]
        change hlhr_intervalContent root (lo, k) ++
            hlhr_intervalTurns root
              (hlhr_intervalsAux f root.length fuel (!up) k) = root.drop lo
        rw [hrec]
        unfold hlhr_intervalContent
        have hdrop : root.drop k = (root.drop lo).drop (k - lo) := by
          rw [List.drop_drop]
          congr 1
          omega
        rw [hdrop]
        exact List.take_append_drop (k - lo) (root.drop lo)
      · have heq : lo = root.length := by omega
        subst lo
        simp [hlhr_intervalsAux, hlhr_intervalTurns]


theorem hlhr_intervalsAux_bounds (f : ℕ → ℝ) (hi fuel lo : ℕ) (up : Bool)
    (hlt : lo < hi) (hahead : HLHRAhead f up lo hi) :
    ∀ p ∈ hlhr_intervalsAux f hi fuel up lo,
      lo ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ hi := by
  induction fuel generalizing up lo with
  | zero => simp [hlhr_intervalsAux]
  | succ fuel ih =>
      intro p hp
      let k := hlhr_lastExtremum f up lo hi
      have hklo : lo < k := by
        dsimp [k]
        exact hlhr_lastExtremum_gt f up hlt hahead
      have hkhi : k ≤ hi := by
        dsimp [k]
        exact hlhr_lastExtremum_le_hi f up (le_of_lt hlt)
      have hnext : HLHRAhead f (!up) k hi := by
        dsimp [k]
        exact hlhr_ahead_next f up hlt
      simp only [hlhr_intervalsAux, hlt, ↓reduceIte, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨le_rfl, hklo, hkhi⟩
      · by_cases hk : k < hi
        · obtain ⟨hkp, hp12, hp2hi⟩ := ih k (!up) hk hnext p hp
          exact ⟨le_trans (le_of_lt hklo) hkp, hp12, hp2hi⟩
        · have hkeq : k = hi := by omega
          have htailNil : hlhr_intervalsAux f hi fuel (!up) k = [] := by
            rw [hkeq]
            cases fuel <;> simp [hlhr_intervalsAux]
          rw [htailNil] at hp
          simp at hp


end StatMech.Universality
