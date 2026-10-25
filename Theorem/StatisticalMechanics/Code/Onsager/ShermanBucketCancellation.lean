/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanBucketCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanGenericCancellation.Part3
import Theorem.StatisticalMechanics.Code.Onsager.ShermanHlam


namespace StatMech.Onsager

open Matrix BigOperators Finset

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem validRootedList_ofFn_append (e r : E) (her : e ≠ r)
    {n : ℕ} (v : Fin (n + 1) → E) :
    ons_validRootedList e r (List.ofFn v ++ [e]) ↔
      v 0 = e ∧ ∀ j, v j ≠ r := by
  unfold ons_validRootedList
  constructor
  · rintro ⟨hhead, _, havoid⟩
    have hroot : v 0 = e := by simpa [List.ofFn_succ] using hhead
    refine ⟨hroot, fun j => havoid (v j) ?_⟩
    rw [List.mem_append, List.mem_ofFn]
    exact Or.inl ⟨j, rfl⟩
  · rintro ⟨hroot, havoid⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [List.ofFn_succ] using hroot
    · rw [List.getLast?_append_of_ne_nil _ (by simp : [e] ≠ [])]
      simp
    · intro x hx
      rw [List.mem_append, List.mem_ofFn, List.mem_singleton] at hx
      rcases hx with ⟨j, rfl⟩ | rfl
      · exact havoid j
      · exact her

theorem rootedListTerm_ofFn_append (Lambda : Matrix E E ℂ) (e : E)
    {n : ℕ} (v : Fin (n + 1) → E) (hroot : v 0 = e) :
    ons_rootedListTerm Lambda e (List.ofFn v ++ [e]) =
      ons_loopWeight Lambda v / (ons_visitCount e v : ℂ) := by
  unfold ons_rootedListTerm
  rw [ons_firstReturnFactors_length e v hroot]
  rw [ons_loopWeight_eq_edgeWeight, hroot]

theorem ofFn_snoc (a : E) {n : ℕ} (v : Fin (n + 1) → E) :
    List.ofFn (Fin.snoc v a : Fin (n + 2) → E) = List.ofFn v ++ [a] := by
  rw [List.ofFn_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  exact List.concat_eq_append

end StatMech.Onsager
