/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Def.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part10
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem hexagonalPairOrbitFrom_to (e : Sym2 HexVertex) :
    hexagonalPairOrbitFrom (hexagonalPairOrbitTo e) = e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      rw [hexagonalPairOrbitTo_mk]
      unfold hexagonalPairNormal
      split_ifs with h hr hb
      · simp only [hexagonalPairOrbitFrom]
        congr 1
        apply Prod.ext
        · simp
        · rfl
      · simp only [hexagonalPairOrbitFrom]
        rw [show v.1 + (u.1 - v.1) = u.1 by abel]
        exact Sym2.eq_swap
      · have hz : v.1 - u.1 = 0 := by
          apply site_eq_zero_of_not_lexPositive_or_neg h
          simpa only [neg_sub] using hr
        have hvu : v.1 = u.1 := sub_eq_zero.mp hz
        rcases u with ⟨ux, ub⟩
        rcases v with ⟨vx, vb⟩
        simp only at hvu
        subst vx
        simp only [hexagonalPairOrbitFrom]
      · have hz : v.1 - u.1 = 0 := by
          apply site_eq_zero_of_not_lexPositive_or_neg h
          simpa only [neg_sub] using hr
        have hvu : v.1 = u.1 := sub_eq_zero.mp hz
        rcases u with ⟨ux, ub⟩
        rcases v with ⟨vx, vb⟩
        simp only at hvu
        subst vx
        simp only [hexagonalPairOrbitFrom]
        exact Sym2.eq_swap

theorem hexagonalPairOrbitTo_from
    (a : Site 2 × HexagonalPairShape) :
    hexagonalPairOrbitTo (hexagonalPairOrbitFrom a) = a := by
  rcases a with ⟨x, s⟩
  rcases s with s | s
  · rcases s with ⟨d, b, c⟩
    rcases d with ⟨d, hd⟩
    rw [show hexagonalPairOrbitFrom
      (x, Sum.inl (⟨d, hd⟩, b, c)) =
        s((x, b), (x + d, c)) by rfl]
    rw [hexagonalPairOrbitTo_mk]
    unfold hexagonalPairNormal
    simp only [add_sub_cancel_left, hd, dite_true]
  · rcases s with ⟨⟨b, c⟩, hbc⟩
    rw [show hexagonalPairOrbitFrom
      (x, Sum.inr ⟨(b, c), hbc⟩) = s((x, b), (x, c)) by rfl]
    rw [hexagonalPairOrbitTo_mk]
    unfold hexagonalPairNormal
    simp only [sub_self]
    have hn : ¬ siteLexPositive (0 : Site 2) := by
      simp [siteLexPositive]
    simp only [hn, dite_false, hbc, dite_true]


end StatMech.FK.PeriodicPlanar
