/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface.Part10
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem preferenceTriangleSideTrueFalse_color {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) (k : Fin 3)
    (hactive : preferenceTriangleSideActive color t k) :
    color (preferenceTriangleSideTrue color t k) = true ∧
      color (preferenceTriangleSideFalse color t k) = false := by
  unfold preferenceTriangleSideActive at hactive
  by_cases ha : color (preferenceTriangleVertex t k) = true
  · have hb : color (preferenceTriangleVertex t (preferenceTriangleNext k)) =
        false := by
      cases hbc : color (preferenceTriangleVertex t (preferenceTriangleNext k)) <;>
        simp_all
    simp [preferenceTriangleSideTrue, preferenceTriangleSideFalse, ha, hb]
  · have ha' : color (preferenceTriangleVertex t k) = false := by
      cases hac : color (preferenceTriangleVertex t k) <;> simp_all
    have hb : color (preferenceTriangleVertex t (preferenceTriangleNext k)) =
        true := by
      cases hbc : color (preferenceTriangleVertex t (preferenceTriangleNext k)) <;>
        simp_all
    simp [preferenceTriangleSideTrue, preferenceTriangleSideFalse, ha, ha', hb]

theorem preferenceTriangleSide_king {n m : Nat}
    (t : PreferenceTriangle n m) (k : Fin 3) :
    KingAdj
      (preferenceGridSite (preferenceTriangleVertex t k))
      (preferenceGridSite
        (preferenceTriangleVertex t (preferenceTriangleNext k))) := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> fin_cases k <;>
    simp [preferenceTriangleVertex, preferenceTriangleNext,
      preferenceGridSite, KingAdj] <;> norm_num
  all_goals
    intro h
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    simp [preferenceGridSite] at h0 h1

theorem preferenceTriangleSideTrueFalse_king {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) (k : Fin 3) :
    KingAdj
      (preferenceGridSite (preferenceTriangleSideTrue color t k))
      (preferenceGridSite (preferenceTriangleSideFalse color t k)) := by
  unfold preferenceTriangleSideTrue preferenceTriangleSideFalse
  split_ifs
  · exact preferenceTriangleSide_king t k
  · exact (preferenceTriangleSide_king t k).symm

theorem preferenceTriangleVertex_king_or_eq {n m : Nat}
    (t : PreferenceTriangle n m) (k l : Fin 3) :
    preferenceTriangleVertex t k = preferenceTriangleVertex t l ∨
      KingAdj
        (preferenceGridSite (preferenceTriangleVertex t k))
        (preferenceGridSite (preferenceTriangleVertex t l)) := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> fin_cases k <;> fin_cases l <;>
    simp [preferenceTriangleVertex, preferenceGridSite, KingAdj] <;> norm_num
  all_goals
    right
    intro h
    have h0 := congrFun h (0 : Fin 2)
    have h1 := congrFun h (1 : Fin 2)
    simp [preferenceGridSite] at h0 h1

theorem preferenceTriangleSideTrue_king_or_eq {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t : PreferenceTriangle n m) (k l : Fin 3) :
    preferenceTriangleSideTrue color t k =
        preferenceTriangleSideTrue color t l ∨
      KingAdj
        (preferenceGridSite (preferenceTriangleSideTrue color t k))
        (preferenceGridSite (preferenceTriangleSideTrue color t l)) := by
  unfold preferenceTriangleSideTrue
  split_ifs <;> apply preferenceTriangleVertex_king_or_eq

theorem preferenceTriangleOther_reciprocal_vertices {n m : Nat}
    (t s : PreferenceTriangle n m) (k : Fin 3)
    (hforward : preferenceTriangleOther t k = .triangle s) :
    ∃ l : Fin 3,
      preferenceTriangleOther s l = .triangle t ∧
      preferenceTriangleVertex s l =
        preferenceTriangleVertex t (preferenceTriangleNext k) ∧
      preferenceTriangleVertex s (preferenceTriangleNext l) =
        preferenceTriangleVertex t k := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> fin_cases k <;>
    simp [preferenceTriangleOther] at hforward
  all_goals (try split_ifs at hforward)
  all_goals (try simp at hforward)
  all_goals subst s
  · refine ⟨1, ?_, ?_, ?_⟩
    · have hjm : j.val - 1 + 1 ≠ m := by omega
      have hj : (⟨j.val - 1 + 1, by omega⟩ : Fin m) = j := by
        apply Fin.ext
        dsimp
        omega
      simp [preferenceTriangleOther, hjm, hj]
    · have hj : (⟨j.val - 1, by omega⟩ : Fin m).succ = j.castSucc := by
        apply Fin.ext
        dsimp
        omega
      simp [preferenceTriangleVertex, preferenceTriangleNext, hj]
    · have hj : (⟨j.val - 1, by omega⟩ : Fin m).succ = j.castSucc := by
        apply Fin.ext
        dsimp
        omega
      simp [preferenceTriangleVertex, preferenceTriangleNext, hj]
  · refine ⟨2, ?_, ?_, ?_⟩
    · simp [preferenceTriangleOther, Fin.ext_iff]
    · simp [preferenceTriangleVertex, preferenceTriangleNext, Fin.ext_iff]
    · simp [preferenceTriangleVertex, preferenceTriangleNext, Fin.ext_iff]
  · refine ⟨0, by simp [preferenceTriangleOther], ?_, ?_⟩ <;>
      simp [preferenceTriangleVertex, preferenceTriangleNext]
  · refine ⟨2, by simp [preferenceTriangleOther], ?_, ?_⟩ <;>
      simp [preferenceTriangleVertex, preferenceTriangleNext]
  · refine ⟨0, ?_, ?_, ?_⟩
    · simp [preferenceTriangleOther, Fin.ext_iff]
    · simp [preferenceTriangleVertex, preferenceTriangleNext, Fin.ext_iff]
    · simp [preferenceTriangleVertex, preferenceTriangleNext, Fin.ext_iff]
  · refine ⟨1, ?_, ?_, ?_⟩
    · have hin : i.val - 1 + 1 ≠ n := by omega
      have hi : (⟨i.val - 1 + 1, by omega⟩ : Fin n) = i := by
        apply Fin.ext
        dsimp
        omega
      simp [preferenceTriangleOther, hin, hi]
    · have hi : (⟨i.val - 1, by omega⟩ : Fin n).succ = i.castSucc := by
        apply Fin.ext
        dsimp
        omega
      simp [preferenceTriangleVertex, preferenceTriangleNext, hi]
    · have hi : (⟨i.val - 1, by omega⟩ : Fin n).succ = i.castSucc := by
        apply Fin.ext
        dsimp
        omega
      simp [preferenceTriangleVertex, preferenceTriangleNext, hi]

theorem preferenceTriangleSideTrue_swap {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (a b : PreferenceGridVertex n m) (h : color a ≠ color b) :
    (if color a = true then a else b) =
      (if color b = true then b else a) := by
  cases ha : color a <;> cases hb : color b <;> simp_all

theorem preferenceTriangleSideTrue_reciprocal_exists {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t s : PreferenceTriangle n m) (k : Fin 3)
    (hforward : preferenceTriangleOther t k = .triangle s)
    (hactive : preferenceTriangleSideActive color t k) :
    ∃ l : Fin 3,
      preferenceTriangleOther s l = .triangle t ∧
      preferenceTriangleSideActive color s l ∧
      preferenceTriangleSideTrue color t k =
        preferenceTriangleSideTrue color s l := by
  obtain ⟨l, hback, hfirst, hsecond⟩ :=
    preferenceTriangleOther_reciprocal_vertices t s k hforward
  obtain ⟨l', hback', hactive'⟩ :=
    preferenceTriangleOther_reciprocal color t s k hforward
  have hll : l' = l := preferenceTriangleOther_injective s
    (hback'.trans hback.symm)
  subst l'
  refine ⟨l, hback, hactive'.2 hactive, ?_⟩
  unfold preferenceTriangleSideTrue
  rw [hfirst, hsecond]
  exact preferenceTriangleSideTrue_swap color _ _ hactive

end StatMech.FK.PeriodicPlanar
