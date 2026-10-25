/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface.Part11
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem preferenceSideBoundaryPoint_reachable_sameTriangle {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) (k l : Fin 3)
    (hk : preferenceTriangleSideActive color t k)
    (hl : preferenceTriangleSideActive color t l) :
    (preferenceGridBoundaryGraph color).Reachable
      (preferenceSideBoundaryPoint color t k hk)
      (preferenceSideBoundaryPoint color t l hl) := by
  rcases preferenceTriangleSideTrue_king_or_eq color t k l with heq | hadj
  · have hpoint : preferenceSideBoundaryPoint color t k hk =
        preferenceSideBoundaryPoint color t l hl := Subtype.ext heq
    rw [hpoint]
  · apply Adj.reachable
    change KingAdj
      (preferenceGridSite (n := n) (m := m)
        (preferenceTriangleSideTrue color t k))
      (preferenceGridSite (n := n) (m := m)
      (preferenceTriangleSideTrue color t l))
    exact hadj

theorem PreferenceRightFlagChain.boundaryReachable {n m : Nat}
    {color : PreferenceGridVertex n m → Bool}
    {t : PreferenceTriangle n m}
    (chain : PreferenceRightFlagChain color t) :
    ∀ (incoming : Fin 3)
      (hincoming : preferenceTriangleSideActive color t incoming),
      ∃ (lastTriangle : PreferenceTriangle n m) (lastSide : Fin 3)
        (hlast : preferenceTriangleSideActive color lastTriangle lastSide),
        preferenceTriangleOther lastTriangle lastSide = .right ∧
        (preferenceGridBoundaryGraph color).Reachable
          (preferenceSideBoundaryPoint color t incoming hincoming)
          (preferenceSideBoundaryPoint color lastTriangle lastSide hlast) := by
  induction chain with
  | @last t k hk hright =>
      intro incoming hincoming
      exact ⟨t, k, hk, hright,
        preferenceSideBoundaryPoint_reachable_sameTriangle
          color t incoming k hincoming hk⟩
  | @cons t s k hk hnext tail ih =>
      intro incoming hincoming
      obtain ⟨l, hback, hl, heq⟩ :=
        preferenceTriangleSideTrue_reciprocal_exists
          color t s k hnext hk
      obtain ⟨lastTriangle, lastSide, hlast, hright, htail⟩ := ih l hl
      have hlocal := preferenceSideBoundaryPoint_reachable_sameTriangle
        color t incoming k hincoming hk
      have hbridge : (preferenceGridBoundaryGraph color).Reachable
          (preferenceSideBoundaryPoint color t k hk)
          (preferenceSideBoundaryPoint color s l hl) := by
        have hp : preferenceSideBoundaryPoint color t k hk =
            preferenceSideBoundaryPoint color s l hl := Subtype.ext heq
        rw [hp]
      exact ⟨lastTriangle, lastSide, hlast, hright,
        hlocal.trans (hbridge.trans htail)⟩

theorem preferenceTriangleSideTrue_col_zero_of_left {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) (k : Fin 3)
    (hleft : preferenceTriangleOther t k = .left) :
    (preferenceTriangleSideTrue color t k).1.val = 0 := by
  obtain ⟨hupper, hcol, rfl⟩ :=
    (preferenceTriangleOther_eq_left_iff t k).1 hleft
  rcases t with ⟨i, j, upper⟩
  dsimp at hupper hcol ⊢
  subst upper
  unfold preferenceTriangleSideTrue
  simp only [preferenceTriangleVertex, preferenceTriangleNext,
    Bool.true_eq_false, if_false]
  split_ifs <;> simpa using hcol

theorem preferenceTriangleSideTrue_col_right_of_right {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) (k : Fin 3)
    (hright : preferenceTriangleOther t k = .right) :
    (preferenceTriangleSideTrue color t k).1.val = n := by
  obtain ⟨hupper, hcol, rfl⟩ :=
    (preferenceTriangleOther_eq_right_iff t k).1 hright
  rcases t with ⟨i, j, upper⟩
  dsimp at hupper hcol ⊢
  subst upper
  unfold preferenceTriangleSideTrue
  simp only [preferenceTriangleVertex, preferenceTriangleNext,
    Bool.false_eq_true, if_false]
  split_ifs <;> simpa using hcol

theorem preferenceGridBoundary_color_data {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (x : PreferenceGridVertex n m) (hx : x ∈ preferenceGridBoundary color) :
    color x = true ∧
      ∃ y : PreferenceGridVertex n m,
        KingAdj (preferenceGridSite x) (preferenceGridSite y) ∧
        color y = false := by
  obtain ⟨t, k, hk, rfl⟩ := hx
  obtain ⟨htrue, hfalse⟩ := preferenceTriangleSideTrueFalse_color color t k hk
  exact ⟨htrue, preferenceTriangleSideFalse color t k,
    preferenceTriangleSideTrueFalse_king color t k, hfalse⟩

theorem preferenceGridBoundary_reachable_left_right_of_flagCrossing
    {n m : Nat} (color : PreferenceGridVertex n m → Bool)
    (hcross : PreferenceFlagCrossing color) :
    ∃ (leftPoint rightPoint : {x // x ∈ preferenceGridBoundary color}),
      leftPoint.val.1.val = 0 ∧ rightPoint.val.1.val = n ∧
      (preferenceGridBoundaryGraph color).Reachable leftPoint rightPoint := by
  obtain ⟨t, k, hk, hleft, chain⟩ := hcross
  obtain ⟨lastTriangle, lastSide, hlast, hright, hreach⟩ :=
    chain.boundaryReachable k hk
  exact ⟨preferenceSideBoundaryPoint color t k hk,
    preferenceSideBoundaryPoint color lastTriangle lastSide hlast,
    preferenceTriangleSideTrue_col_zero_of_left color t k hleft,
    preferenceTriangleSideTrue_col_right_of_right
      color lastTriangle lastSide hright,
    hreach⟩

theorem preferenceGridSite_injective {n m : Nat} :
    Function.Injective (preferenceGridSite : PreferenceGridVertex n m → Site 2) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  apply Prod.ext
  · apply Fin.ext
    have h0 := congrFun h (0 : Fin 2)
    simp [preferenceGridSite] at h0
    exact_mod_cast h0
  · apply Fin.ext
    have h1 := congrFun h (1 : Fin 2)
    simp [preferenceGridSite] at h1
    exact_mod_cast h1

end StatMech.FK.PeriodicPlanar
