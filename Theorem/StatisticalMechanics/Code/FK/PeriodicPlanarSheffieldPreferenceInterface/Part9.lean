/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface.Part8
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem preferenceLeftActiveRows_card {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) (hn : 0 < n) :
    (preferenceLeftActiveRows (n := n) (m := m) color hn).card =
      finBoolTransitionCount
        (preferenceLeftColor (n := n) (m := m) color) := by
  unfold finBoolTransitionCount
  unfold preferenceLeftActiveRows
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _hj
  have hside :
      preferenceTriangleSideActive color (preferenceLeftTriangle hn j) 2 ↔
        preferenceLeftColor color j.castSucc ≠
          preferenceLeftColor color j.succ := by
    simp only [preferenceTriangleSideActive, preferenceLeftTriangle,
      preferenceTriangleVertex, preferenceTriangleNext, preferenceLeftColor,
      Bool.true_eq_false, if_false]
    constructor <;> exact fun hne heq => hne heq.symm
  by_cases hs : preferenceTriangleSideActive color
      (preferenceLeftTriangle hn j) 2
  · have hne := hside.1 hs
    simp [hs, hne]
  · have heq : preferenceLeftColor color j.castSucc =
        preferenceLeftColor color j.succ := by
      by_contra hne
      exact hs (hside.2 hne)
    simp [hs, heq]

theorem preferenceInterface_left_odd_degree {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) (hn : 0 < n)
    (hend : preferenceLeftColor (n := n) (m := m) color 0 ≠
      preferenceLeftColor (n := n) (m := m) color (Fin.last m)) :
    Odd ((preferenceInterfaceGraph color).degree (.left)) := by
  rw [preferenceInterface_degree_left (hn := hn),
    preferenceLeftActiveRows_card (hn := hn)]
  exact finBoolTransitionCount_odd _ hend

theorem preferenceInterface_exterior_degree_zero {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (side : PreferenceInterfaceNode n m)
    (hside : ∀ t : PreferenceTriangle n m, side ≠ .triangle t)
    (hinactive : ∀ (t : PreferenceTriangle n m) (k : Fin 3),
      preferenceTriangleOther t k = side →
        ¬preferenceTriangleSideActive color t k) :
    (preferenceInterfaceGraph color).degree side = 0 := by
  rw [degree_eq_zero]
  intro v hadj
  change preferenceInterfaceAdj color side v at hadj
  rw [preferenceInterfaceAdj_exterior_iff color side hside] at hadj
  obtain ⟨t, k, hk, hother, _hv⟩ := hadj
  exact hinactive t k hother hk

theorem preferenceInterface_bottom_degree_zero {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) (b : Bool)
    (hbottom : ∀ i : Fin (n + 1), color (i, 0) = b) :
    (preferenceInterfaceGraph color).degree (.bottom) = 0 := by
  apply preferenceInterface_exterior_degree_zero color .bottom (by simp)
  intro t k hother
  obtain ⟨hupper, hrow, rfl⟩ :=
    (preferenceTriangleOther_eq_bottom_iff t k).1 hother
  rcases t with ⟨i, j, upper⟩
  dsimp at hupper hrow ⊢
  subst upper
  have hj : j.castSucc = (0 : Fin (m + 1)) := Fin.ext hrow
  simp only [preferenceTriangleSideActive, preferenceTriangleVertex,
    preferenceTriangleNext, Bool.false_eq_true, if_false]
  rw [hj, hbottom, hbottom]
  simp

theorem preferenceInterface_top_degree_zero {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) (b : Bool)
    (htop : ∀ i : Fin (n + 1), color (i, Fin.last m) = b) :
    (preferenceInterfaceGraph color).degree (.top) = 0 := by
  apply preferenceInterface_exterior_degree_zero color .top (by simp)
  intro t k hother
  obtain ⟨hupper, hrow, rfl⟩ :=
    (preferenceTriangleOther_eq_top_iff t k).1 hother
  rcases t with ⟨i, j, upper⟩
  dsimp at hupper hrow ⊢
  subst upper
  have hj : j.succ = Fin.last m := by
    apply Fin.ext
    exact hrow
  simp only [preferenceTriangleSideActive, preferenceTriangleVertex,
    preferenceTriangleNext, if_true]
  rw [hj, htop, htop]
  simp

theorem preferenceInterface_left_reachable_right {n m : Nat}
    (color : PreferenceGridVertex n m → Bool) (hn : 0 < n)
    (bottomColor topColor : Bool)
    (hbottom : ∀ i : Fin (n + 1), color (i, 0) = bottomColor)
    (htop : ∀ i : Fin (n + 1),
      color (i, Fin.last m) = topColor)
    (hne : bottomColor ≠ topColor) :
    (preferenceInterfaceGraph color).Reachable (.left) (.right) := by
  classical
  apply reachable_of_only_two_odd_degree
    (preferenceInterfaceGraph color) .left .right
  · apply preferenceInterface_left_odd_degree color hn
    simpa [preferenceLeftColor, hbottom, htop] using hne
  · intro v hv
    cases v with
    | left => exact Or.inl rfl
    | right => exact Or.inr rfl
    | bottom =>
        have hz := preferenceInterface_bottom_degree_zero
          color bottomColor hbottom
        rw [hz] at hv
        simp at hv
    | top =>
        have hz := preferenceInterface_top_degree_zero color topColor htop
        rw [hz] at hv
        simp at hv
    | triangle t =>
        exact ((Nat.not_even_iff_odd.mpr hv)
          (preferenceInterface_triangle_even_degree color t)).elim

end StatMech.FK.PeriodicPlanar
