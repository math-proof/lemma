/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface.Part4
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem preferenceTriangleOther_ne_self {n m : Nat}
    (t : PreferenceTriangle n m) (k : Fin 3) :
    preferenceTriangleOther t k ≠ .triangle t := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> fin_cases k <;> simp [preferenceTriangleOther] <;>
    split_ifs <;> simp

theorem fin_succ_ne_self {n : Nat} (i : Fin n)
    (h : i.val + 1 < n) : (⟨i.val + 1, h⟩ : Fin n) ≠ i := by
  intro hi
  have := congrArg Fin.val hi
  change i.val + 1 = i.val at this
  omega

theorem fin_pred_ne_self {n : Nat} (i : Fin n)
    (h0 : i.val ≠ 0) (h : i.val - 1 < n) :
    (⟨i.val - 1, h⟩ : Fin n) ≠ i := by
  intro hi
  have := congrArg Fin.val hi
  change i.val - 1 = i.val at this
  omega

theorem fin_self_ne_succ {n : Nat} (i : Fin n)
    (h : i.val + 1 < n) : i ≠ (⟨i.val + 1, h⟩ : Fin n) :=
  (fin_succ_ne_self i h).symm

theorem fin_self_ne_pred {n : Nat} (i : Fin n)
    (h0 : i.val ≠ 0) (h : i.val - 1 < n) :
    i ≠ (⟨i.val - 1, h⟩ : Fin n) :=
  (fin_pred_ne_self i h0 h).symm

theorem preferenceTriangleOther_zero_ne_one {n m : Nat}
    (t : PreferenceTriangle n m) :
    preferenceTriangleOther t 0 ≠ preferenceTriangleOther t 1 := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> simp [preferenceTriangleOther] <;>
    split_ifs <;> simp_all [fin_succ_ne_self, fin_pred_ne_self,
      fin_self_ne_succ, fin_self_ne_pred]

theorem preferenceTriangleOther_zero_ne_two {n m : Nat}
    (t : PreferenceTriangle n m) :
    preferenceTriangleOther t 0 ≠ preferenceTriangleOther t 2 := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> simp [preferenceTriangleOther] <;>
    split_ifs <;> simp_all [fin_succ_ne_self, fin_pred_ne_self,
      fin_self_ne_succ, fin_self_ne_pred]

theorem preferenceTriangleOther_one_ne_two {n m : Nat}
    (t : PreferenceTriangle n m) :
    preferenceTriangleOther t 1 ≠ preferenceTriangleOther t 2 := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> simp [preferenceTriangleOther] <;>
    split_ifs <;> simp_all [fin_succ_ne_self, fin_pred_ne_self,
      fin_self_ne_succ, fin_self_ne_pred]

theorem preferenceTriangleOther_injective {n m : Nat}
    (t : PreferenceTriangle n m) :
    Function.Injective (preferenceTriangleOther t) := by
  intro k l hkl
  fin_cases k <;> fin_cases l <;> try rfl
  · exact (preferenceTriangleOther_zero_ne_one t hkl).elim
  · exact (preferenceTriangleOther_zero_ne_two t hkl).elim
  · exact (preferenceTriangleOther_zero_ne_one t hkl.symm).elim
  · exact (preferenceTriangleOther_one_ne_two t hkl).elim
  · exact (preferenceTriangleOther_zero_ne_two t hkl.symm).elim
  · exact (preferenceTriangleOther_one_ne_two t hkl.symm).elim

theorem preferenceTriangleOther_reciprocal {n m : Nat}
    (color : PreferenceGridVertex n m → Bool)
    (t s : PreferenceTriangle n m) (k : Fin 3)
    (h : preferenceTriangleOther t k = .triangle s) :
    ∃ l : Fin 3,
      preferenceTriangleOther s l = .triangle t ∧
      (preferenceTriangleSideActive color s l ↔
        preferenceTriangleSideActive color t k) := by
  rcases t with ⟨i, j, upper⟩
  cases upper <;> fin_cases k <;>
    simp [preferenceTriangleOther] at h
  all_goals (try split_ifs at h)
  all_goals (try simp at h)
  all_goals subst s
  · refine ⟨1, ?_, ?_⟩
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
      simp only [preferenceTriangleSideActive, preferenceTriangleVertex,
        preferenceTriangleNext, Bool.false_eq_true, if_false, if_true]
      rw [hj]
      constructor <;> exact fun hne heq => hne heq.symm
  · refine ⟨2, ?_, ?_⟩
    · simp [preferenceTriangleOther, Fin.ext_iff]
    · simp [preferenceTriangleSideActive, preferenceTriangleVertex,
        preferenceTriangleNext, Fin.ext_iff]
      have hi : (⟨i.val + 1, by omega⟩ : Fin (n + 1)) = i.succ := by
        apply Fin.ext
        rfl
      rw [hi]
      constructor <;> exact fun hne heq => hne heq.symm
  · refine ⟨0, by simp [preferenceTriangleOther], ?_⟩
    simp only [preferenceTriangleSideActive, preferenceTriangleVertex,
      preferenceTriangleNext, Bool.false_eq_true, if_true, if_false]
    constructor <;> exact fun hne heq => hne heq.symm
  · refine ⟨2, by simp [preferenceTriangleOther], ?_⟩
    simp only [preferenceTriangleSideActive, preferenceTriangleVertex,
      preferenceTriangleNext, Bool.false_eq_true, if_true, if_false]
    constructor <;> exact fun hne heq => hne heq.symm
  · refine ⟨0, ?_, ?_⟩
    · simp [preferenceTriangleOther, Fin.ext_iff]
    · simp [preferenceTriangleSideActive, preferenceTriangleVertex,
        preferenceTriangleNext, Fin.ext_iff]
      have hj : (⟨j.val + 1, by omega⟩ : Fin (m + 1)) = j.succ := by
        apply Fin.ext
        rfl
      rw [hj]
      constructor <;> exact fun hne heq => hne heq.symm
  · refine ⟨1, ?_, ?_⟩
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
      simp only [preferenceTriangleSideActive, preferenceTriangleVertex,
        preferenceTriangleNext, Bool.false_eq_true, if_true, if_false]
      rw [hi]
      constructor <;> exact fun hne heq => hne heq.symm

end StatMech.FK.PeriodicPlanar
