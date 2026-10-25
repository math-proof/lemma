/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveParity
import Def.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part5


namespace StatMech.Onsager

open BaseCase

theorem onsCyclicDirectionNonUturn_ofFn
    {n : ℕ} [NeZero n] (dir : Fin n → Fin 4)
    (hnu : ∀ k : Fin n, onsDirectionNonUturn (dir k) (dir (k + 1))) :
    onsCyclicDirectionNonUturn (List.ofFn dir) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  constructor
  · rw [List.isChain_ofFn]
    intro i hi
    let k : Fin (m + 1) := ⟨i, by omega⟩
    have hk : k ≠ Fin.last m := by
      intro h
      have := Fin.mk.inj_iff.mp h
      omega
    have hnext : k + 1 = ⟨i + 1, by omega⟩ := by
      apply Fin.ext
      exact Fin.val_add_one_of_lt (lt_of_le_of_ne (Fin.le_last k) hk)
    simpa [k, hnext] using hnu k
  · intro a ha b hb
    rw [List.getLast?_eq_getLast (by simp), List.getLast_ofFn] at ha
    simp only [Option.mem_def, Option.some.injEq] at ha
    rw [List.ofFn_succ] at hb
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
    subst a
    subst b
    simpa using hnu (Fin.last m)

theorem onsCyclicDirectionNonUturn_ofFn_apply
    {n : ℕ} [NeZero n] (dir : Fin n → Fin 4)
    (hcyclic : onsCyclicDirectionNonUturn (List.ofFn dir)) :
    ∀ k : Fin n, onsDirectionNonUturn (dir k) (dir (k + 1)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  intro k
  by_cases hk : k = Fin.last m
  · subst k
    apply hcyclic.2 (dir (Fin.last m))
    · rw [List.getLast?_eq_getLast (by simp), List.getLast_ofFn]
      simp only [Option.mem_def, Option.some.injEq]
      apply congrArg dir
      apply Fin.ext
      simp
    · rw [List.ofFn_succ]
      simp
  · have hklt : k.val < m := by
      have hle := Fin.le_last k
      exact lt_of_le_of_ne hle (fun h => hk (Fin.ext h))
    have hchain := hcyclic.1
    rw [List.isChain_ofFn] at hchain
    have h := hchain k.val (by omega)
    have hnext : k + 1 = ⟨k.val + 1, by omega⟩ := by
      apply Fin.ext
      exact Fin.val_add_one_of_lt (by simpa using hklt)
    simpa [hnext] using h

theorem onsDirectionNonUturn_comm (d e : Fin 4) :
    onsDirectionNonUturn d e ↔ onsDirectionNonUturn e d := by
  fin_cases d <;> fin_cases e <;> simp [onsDirectionNonUturn]


end StatMech.Onsager
