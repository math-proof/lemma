/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Instance.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem preferenceInterface_neighborFinset_triangle {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) :
    (preferenceInterfaceGraph color).neighborFinset (.triangle t) =
      (preferenceActiveSides color t).image (preferenceTriangleOther t) := by
  classical
  ext v
  simp only [mem_neighborFinset, Finset.mem_image, preferenceActiveSides,
    Finset.mem_filter, Finset.mem_univ, true_and]
  change preferenceInterfaceAdj color (.triangle t) v ↔ _
  rw [preferenceInterfaceAdj_triangle_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩

theorem preferenceInterface_degree_triangle {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) :
    (preferenceInterfaceGraph color).degree (.triangle t) =
      (preferenceActiveSides color t).card := by
  classical
  rw [← card_neighborFinset_eq_degree,
    preferenceInterface_neighborFinset_triangle]
  exact Finset.card_image_of_injective _
    (preferenceTriangleOther_injective t)

theorem preferenceActiveSides_card {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) :
    (preferenceActiveSides color t).card =
      boolTriangleTransitionCount
        (color (preferenceTriangleVertex t 0))
        (color (preferenceTriangleVertex t 1))
        (color (preferenceTriangleVertex t 2)) := by
  classical
  unfold preferenceActiveSides
  rw [Finset.card_filter]
  rw [Fin.sum_univ_three]
  unfold preferenceTriangleSideActive preferenceTriangleNext
    boolTriangleTransitionCount
  by_cases h01 : color (preferenceTriangleVertex t 0) =
      color (preferenceTriangleVertex t 1) <;>
    by_cases h12 : color (preferenceTriangleVertex t 1) =
      color (preferenceTriangleVertex t 2) <;>
    by_cases h20 : color (preferenceTriangleVertex t 2) =
      color (preferenceTriangleVertex t 0) <;> simp_all

theorem preferenceInterface_triangle_even_degree {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) :
    Even ((preferenceInterfaceGraph color).degree (.triangle t)) := by
  rw [preferenceInterface_degree_triangle, preferenceActiveSides_card]
  exact boolTriangleTransitionCount_even _ _ _

theorem preferenceTriangleOther_eq_left_iff {n m : Nat}
    (t : PreferenceTriangle n m) (k : Fin 3) :
    preferenceTriangleOther t k = .left ↔
      t.upper = true ∧ t.col.val = 0 ∧ k = 2 := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> fin_cases k <;>
    simp [preferenceTriangleOther] <;> split_ifs <;> simp_all

theorem preferenceTriangleOther_eq_right_iff {n m : Nat}
    (t : PreferenceTriangle n m) (k : Fin 3) :
    preferenceTriangleOther t k = .right ↔
      t.upper = false ∧ t.col.val + 1 = n ∧ k = 1 := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> fin_cases k <;>
    simp [preferenceTriangleOther] <;> split_ifs <;> simp_all

theorem preferenceTriangleOther_eq_bottom_iff {n m : Nat}
    (t : PreferenceTriangle n m) (k : Fin 3) :
    preferenceTriangleOther t k = .bottom ↔
      t.upper = false ∧ t.row.val = 0 ∧ k = 0 := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> fin_cases k <;>
    simp [preferenceTriangleOther] <;> split_ifs <;> simp_all

theorem preferenceTriangleOther_eq_top_iff {n m : Nat}
    (t : PreferenceTriangle n m) (k : Fin 3) :
    preferenceTriangleOther t k = .top ↔
      t.upper = true ∧ t.row.val + 1 = m ∧ k = 1 := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> fin_cases k <;>
    simp [preferenceTriangleOther] <;> split_ifs <;> simp_all

theorem preferenceInterfaceAdj_exterior_iff {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (side : PreferenceInterfaceNode n m)
    (hside : ∀ t : PreferenceTriangle n m, side ≠ .triangle t)
    (v : PreferenceInterfaceNode n m) :
    preferenceInterfaceAdj color side v ↔
      ∃ (t : PreferenceTriangle n m) (k : Fin 3),
        preferenceTriangleSideActive color t k ∧
        preferenceTriangleOther t k = side ∧ v = .triangle t := by
  constructor
  · rintro ⟨t, k, hk, hforward | hbackward⟩
    · exact (hside t hforward.1).elim
    · exact ⟨t, k, hk, hbackward.2.symm, hbackward.1⟩
  · rintro ⟨t, k, hk, hother, rfl⟩
    exact ⟨t, k, hk, Or.inr ⟨rfl, hother.symm⟩⟩

end StatMech.FK.PeriodicPlanar
