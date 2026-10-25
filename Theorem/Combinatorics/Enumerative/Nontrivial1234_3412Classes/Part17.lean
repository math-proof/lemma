/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Fintype.Perm
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Relation
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Order.Fin.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Def.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part17


namespace MetaMathlibExt

lemma ntSemiVal_eq_beta {n j i : ℕ} (hj : j + 1 ≤ n) (hi : i < n) :
    ntSemiVal n j i = ((ntBeta n j hj) ⟨i, hi⟩).val := by
  rw [ntBeta_val]
  unfold ntSemiVal
  by_cases hij : i < j
  · rw [ite_eq_left hij]
    have heq : j + n - 1 - i = n + (j - 1 - i) := by omega
    have ha : j - 1 - i < n := by omega
    rw [heq, Nat.add_mod]
    simp only [Nat.mod_self, zero_add, Nat.mod_eq_of_lt ha]
  · rw [ite_eq_right hij]
    have hlt : j + n - 1 - i < n := by omega
    rw [Nat.mod_eq_of_lt hlt]
    change j + n - 1 - i = n + j - 1 - i
    omega

lemma ntInTB_sound {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : ntInTB n (ntCode σ) = true) :
    ∃ j : ℕ, ∃ hj : j + 1 ≤ n, σ ∈ ntT n j hj := by
  unfold ntInTB at h
  rw [List.any_eq_true] at h
  obtain ⟨j, hjmem, h⟩ := h
  rw [List.any_eq_true] at h
  obtain ⟨p, hpmem, h⟩ := h
  rw [List.any_eq_true] at h
  obtain ⟨q, hqmem, h⟩ := h
  rw [Bool.and_eq_true] at h
  obtain ⟨hpq, hall⟩ := h
  have hjlt := List.mem_range.mp hjmem
  have hplt := List.mem_range.mp hpmem
  have hqlt := List.mem_range.mp hqmem
  have hjn : j + 1 ≤ n := by omega
  have hpq' : p ≠ q := by
    intro heq
    subst q
    simp at hpq
  let P : Fin n := ⟨p, hplt⟩
  let Q : Fin n := ⟨q, hqlt⟩
  have hPQ : P ≠ Q := by
    intro heq
    exact hpq' (congrArg Fin.val heq)
  refine ⟨j, hjn, P, Q, hPQ, ?_⟩
  apply Equiv.Perm.ext
  intro i
  apply Fin.ext
  rw [Equiv.Perm.mul_apply]
  by_cases hiP : i = P
  · subst i
    rw [Equiv.swap_apply_left]
    have heq := (List.all_eq_true.mp hall) p hpmem
    rw [beq_iff_eq] at heq
    rw [ntCode_getD σ p hplt, ite_eq_left rfl,
      ntSemiVal_eq_beta hjn hqlt] at heq
    exact heq
  · by_cases hiQ : i = Q
    · subst i
      rw [Equiv.swap_apply_right]
      have heq := (List.all_eq_true.mp hall) q hqmem
      rw [beq_iff_eq] at heq
      have hqp : q ≠ p := Ne.symm hpq'
      rw [ntCode_getD σ q hqlt, ite_eq_right hqp, ite_eq_left rfl,
        ntSemiVal_eq_beta hjn hplt] at heq
      exact heq
    · rw [Equiv.swap_apply_of_ne_of_ne hiP hiQ]
      have heq := (List.all_eq_true.mp hall) i.val
        (List.mem_range.mpr i.is_lt)
      rw [beq_iff_eq] at heq
      have hip : i.val ≠ p := fun heq' => hiP (Fin.ext heq')
      have hiq : i.val ≠ q := fun heq' => hiQ (Fin.ext heq')
      rw [ntCode_getD σ i.val i.is_lt, ite_eq_right hip, ite_eq_right hiq,
        ntSemiVal_eq_beta hjn i.is_lt] at heq
      exact heq

lemma ntIsGB_of_memG7 {σ : Equiv.Perm (Fin 7)} (hσ : σ ∈ ntG 6) :
    ntIsGB 7 (ntQuads 7) (ntCode σ) = true := by
  simp only [ntIsGB, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨?_, ?_⟩, ntHasPatB_of_pat hσ.2.1⟩, ?_⟩
  · apply bne_iff_ne.mpr
    simp only [ntCode, List.ofFn_succ, List.headD_cons]
    intro heq
    apply hσ.1.1
    apply Fin.ext
    simpa using heq
  · apply bne_iff_ne.mpr
    simp only [ntCode]
    rw [show (List.ofFn fun i : Fin 7 => (σ i).val).getLastD 0 =
      (σ (Fin.last 6)).val by simp [List.ofFn_succ]]
    intro heq
    apply hσ.1.2
    apply Fin.ext
    exact heq
  · apply Bool.eq_false_iff.mpr
    intro hT
    obtain ⟨j, hj, hσT⟩ := ntInTB_sound hT
    exact hσ.2.2 j hj ⟨hσT, hσ.2.1⟩

lemma ntIsGB_of_memG8 {σ : Equiv.Perm (Fin 8)} (hσ : σ ∈ ntG 7) :
    ntIsGB 8 (ntQuads 8) (ntCode σ) = true := by
  simp only [ntIsGB, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨?_, ?_⟩, ntHasPatB_of_pat hσ.2.1⟩, ?_⟩
  · apply bne_iff_ne.mpr
    simp only [ntCode, List.ofFn_succ, List.headD_cons]
    intro heq
    apply hσ.1.1
    apply Fin.ext
    simpa using heq
  · apply bne_iff_ne.mpr
    simp only [ntCode]
    rw [show (List.ofFn fun i : Fin 8 => (σ i).val).getLastD 0 =
      (σ (Fin.last 7)).val by simp [List.ofFn_succ]]
    intro heq
    apply hσ.1.2
    apply Fin.ext
    exact heq
  · apply Bool.eq_false_iff.mpr
    intro hT
    obtain ⟨j, hj, hσT⟩ := ntInTB_sound hT
    exact hσ.2.2 j hj ⟨hσT, hσ.2.1⟩

end MetaMathlibExt
