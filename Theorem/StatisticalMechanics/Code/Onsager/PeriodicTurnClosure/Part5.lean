/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Def.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part5


namespace StatMech.Onsager

open BigOperators

open StatMech.Onsager.BaseCase

theorem ons_periodStateList_isChain {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (r : ℕ) :
    List.IsChain
      (fun a b ↦ ons_periodStateCoord d b =
        ons_periodStateCoord d a + stepOf (d a.2))
      (ons_periodStateList n r) := by
  rw [ons_periodStateList, List.isChain_ofFn]
  intro i hi
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  let j : Fin m := ⟨i, by omega⟩
  have hjc : (j.castSucc : Fin (m + 1)) = ⟨i, by omega⟩ := Fin.ext rfl
  have hjs : (j.succ : Fin (m + 1)) = ⟨i + 1, hi⟩ := Fin.ext rfl
  simp only [ons_periodStateCoord]
  rw [← hjc, ← hjs, ons_pos_succ_cast]
  abel

theorem ons_periodState_boundary {m : ℕ}
    (d : Fin (m + 1) → Fin 4) (r : ℕ) :
    ons_periodStateCoord d (r + 1, 0) =
      ons_periodStateCoord d (r, Fin.last m) +
        stepOf (d (Fin.last m)) := by
  simp only [ons_periodStateCoord]
  rw [NoDoubleWind.pos_zero, zero_add]
  have hlast := ons_pos_last_add_step d
  rw [← ons_pathDisplacement_ofFn d] at hlast
  rw [succ_nsmul]
  rw [← hlast]
  abel

@[simp] theorem ons_periodStateList_head? {n : ℕ} [NeZero n]
    (r : ℕ) :
    (ons_periodStateList n r).head? = some (r, (0 : Fin n)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  simp [ons_periodStateList, List.ofFn_succ]

end StatMech.Onsager
