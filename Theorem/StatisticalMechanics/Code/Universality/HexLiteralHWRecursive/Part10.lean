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
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part10


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hlhr_piecesAux_reconstruct (f : ℕ → ℝ) (hi fuel lo : ℕ) (up : Bool)
    (ts : List ℤ) :
    hlhr_pieceTurns (hlhr_piecesAux f hi fuel up lo ts) = ts := by
  induction fuel generalizing up lo ts with
  | zero =>
      by_cases hts : ts = []
      · simp [hlhr_piecesAux, hlhr_pieceTurns, hts]
      · simp [hlhr_piecesAux, hlhr_pieceTurns, hts]
  | succ fuel ih =>
      classical
      by_cases hts : ts = []
      · simp [hlhr_piecesAux, hlhr_pieceTurns, hts]
      · simp only [hlhr_piecesAux, hts, ↓reduceDIte, hlhr_pieceTurns,
          List.map_cons, List.flatten_cons]
        change ts.take (hlhr_cut f up lo hi - lo) ++
            hlhr_pieceTurns
              (hlhr_piecesAux f hi fuel (!up) (hlhr_cut f up lo hi)
                (ts.drop (hlhr_cut f up lo hi - lo))) = ts
        rw [ih]
        exact List.take_append_drop _ _


theorem hlhr_pieces_reconstruct (f : ℕ → ℝ) (ts : List ℤ) :
    hlhr_pieceTurns (hlhr_pieces f ts) = ts := by
  unfold hlhr_pieces
  exact hlhr_piecesAux_reconstruct f ts.length ts.length 0 true ts


theorem hlhr_piecesAux_slice (f : ℕ → ℝ) (root : List ℤ) (fuel : ℕ)
    (up : Bool) (lo : ℕ) (hlo : lo ≤ root.length) :
    ∀ p ∈ hlhr_piecesAux f root.length fuel up lo (root.drop lo),
      p.2 = (root.drop p.1).take p.2.length ∧
        p.1 + p.2.length ≤ root.length := by
  induction fuel generalizing up lo with
  | zero =>
      intro p hp
      by_cases hempty : root.drop lo = []
      · simp [hlhr_piecesAux, hempty] at hp
      · simp only [hlhr_piecesAux, hempty, ↓reduceIte, List.mem_singleton] at hp
        rcases hp with rfl
        constructor
        · simp
        · simp [List.length_drop, hlo]
  | succ fuel ih =>
      intro p hp
      by_cases hempty : root.drop lo = []
      · simp [hlhr_piecesAux, hempty] at hp
      · have hlt : lo < root.length := by
          rw [List.drop_eq_nil_iff] at hempty
          omega
        let k := hlhr_cut f up lo root.length
        let d := k - lo
        have hlok : lo < k := by
          dsimp [k]
          exact hlhr_cut_gt f up hlt
        have hkhi : k ≤ root.length := by
          dsimp [k]
          exact hlhr_cut_le f up (le_of_lt hlt)
        have hdpos : 0 < d := by dsimp [d]; omega
        have hdle : d ≤ (root.drop lo).length := by
          simp only [List.length_drop]
          dsimp [d]
          omega
        simp only [hlhr_piecesAux, hempty, ↓reduceDIte, List.mem_cons] at hp
        rcases hp with hp | hp
        · rcases hp with rfl
          have hdirect : hlhr_cut f up lo root.length - lo ≤
              (root.drop lo).length := by
            simpa [k, d] using hdle
          constructor
          · simp only
            rw [List.length_take_of_le hdirect]
          · simp only
            rw [List.length_take_of_le hdirect]
            omega
        · have hdrop : (root.drop lo).drop d = root.drop k := by
            rw [List.drop_drop]
            congr 1
            dsimp [d]
            omega
          rw [hdrop] at hp
          exact ih (!up) k hkhi p hp


theorem hlhr_pieces_slice (f : ℕ → ℝ) (root : List ℤ) :
    ∀ p ∈ hlhr_pieces f root,
      p.2 = (root.drop p.1).take p.2.length ∧
        p.1 + p.2.length ≤ root.length := by
  unfold hlhr_pieces
  exact hlhr_piecesAux_slice f root root.length true 0 (by omega)


theorem hlhr_piecesAux_content_ne (f : ℕ → ℝ) (root : List ℤ) (fuel : ℕ)
    (up : Bool) (lo : ℕ) (hlo : lo ≤ root.length) :
    ∀ p ∈ hlhr_piecesAux f root.length fuel up lo (root.drop lo), p.2 ≠ [] := by
  induction fuel generalizing up lo with
  | zero =>
      intro p hp
      by_cases hempty : root.drop lo = []
      · simp [hlhr_piecesAux, hempty] at hp
      · simp only [hlhr_piecesAux, hempty, ↓reduceIte, List.mem_singleton] at hp
        simpa [hp] using hempty
  | succ fuel ih =>
      intro p hp
      by_cases hempty : root.drop lo = []
      · simp [hlhr_piecesAux, hempty] at hp
      · have hlt : lo < root.length := by
          rw [List.drop_eq_nil_iff] at hempty
          omega
        let k := hlhr_cut f up lo root.length
        let d := k - lo
        have hlok : lo < k := by
          dsimp [k]
          exact hlhr_cut_gt f up hlt
        have hkhi : k ≤ root.length := by
          dsimp [k]
          exact hlhr_cut_le f up (le_of_lt hlt)
        have hdpos : 0 < d := by dsimp [d]; omega
        have hdle : d ≤ (root.drop lo).length := by
          simp only [List.length_drop]
          dsimp [d]
          omega
        simp only [hlhr_piecesAux, hempty, ↓reduceDIte, List.mem_cons] at hp
        rcases hp with hp | hp
        · rcases hp with rfl
          intro hnil
          have hlen := congrArg List.length hnil
          rw [List.length_take_of_le hdle] at hlen
          simp only [List.length_nil] at hlen
          omega
        · have hdrop : (root.drop lo).drop d = root.drop k := by
            rw [List.drop_drop]
            congr 1
            dsimp [d]
            omega
          rw [hdrop] at hp
          exact ih (!up) k hkhi p hp


theorem hlhr_pieces_content_ne (f : ℕ → ℝ) (root : List ℤ) :
    ∀ p ∈ hlhr_pieces f root, p.2 ≠ [] := by
  unfold hlhr_pieces
  exact hlhr_piecesAux_content_ne f root root.length true 0 (by omega)


end StatMech.Universality
