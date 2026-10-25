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
import Def.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part9


namespace MetaMathlibExt

lemma ntBeta_eq_cycle_rev {n j : ℕ} (hj : j + 1 ≤ n) :
    ntBeta n j hj = finCycle (⟨j, by omega⟩ : Fin n) *
      (Fin.revPerm : Equiv.Perm (Fin n)) := by
  apply Equiv.Perm.ext
  intro i
  apply Fin.ext
  rw [ntBeta_val, Equiv.Perm.mul_apply, finCycle_apply, Fin.revPerm_apply,
    Fin.val_add_eq_ite]
  simp only [Fin.val_rev]
  by_cases hij : i.val < j
  · rw [ite_eq_left hij]
    split <;> omega
  · rw [ite_eq_right hij]
    split <;> omega

lemma ntBeta_breaks_eq_empty {n j : ℕ} (hj : j + 1 ≤ n) :
    ntBreaks (ntBeta n j hj) = ∅ := by
  let _ : NeZero n := ⟨by omega⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  rw [nt_mem_breaks_iff] at hi
  apply hi
  rw [ntBeta_eq_cycle_rev hj]
  simp only [Equiv.Perm.mul_apply, finCycle_apply, Fin.revPerm_apply,
    finRotate_apply, finRotate_symm_apply]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  simp only [← Fin.last_sub]
  abel

lemma nt_exists_beta_of_breaks_empty {n : ℕ} (hn : 0 < n)
    {π : Equiv.Perm (Fin n)} (hbreak : ntBreaks π = ∅) :
    ∃ j : ℕ, ∃ hj : j + 1 ≤ n, π = ntBeta n j hj := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hgood : ∀ i : Fin (r + 1),
      π (finRotate (r + 1) i) = (finRotate (r + 1)).symm (π i) := by
    intro i
    by_contra h
    have hi : i ∈ ntBreaks π := (nt_mem_breaks_iff π i).2 h
    rw [hbreak] at hi
    simp at hi
  let jf : Fin (r + 1) := π 0 + 1
  have hform : ∀ k : ℕ, ∀ hk : k < r + 1,
      π (⟨k, hk⟩ : Fin (r + 1)) = (⟨k, hk⟩ : Fin (r + 1)).rev + jf := by
    intro k
    induction k with
    | zero =>
        intro hk
        rw [← Fin.last_sub]
        have hlast : Fin.last r = (-1 : Fin (r + 1)) := by
          apply Fin.ext
          simp
        rw [hlast]
        have hz : (⟨0, hk⟩ : Fin (r + 1)) = 0 := Fin.ext rfl
        rw [hz]
        simp only [sub_zero, jf]
        abel
    | succ k ih =>
        intro hk
        have hkr : k < r := by omega
        have hg := hgood (⟨k, by omega⟩ : Fin (r + 1))
        rw [finRotate_of_lt hkr, finRotate_symm_apply, ih (by omega)] at hg
        rw [hg]
        have hs : (⟨k + 1, hk⟩ : Fin (r + 1)) =
            (⟨k, by omega⟩ : Fin (r + 1)) + 1 := by
          apply Fin.ext
          rw [Fin.val_add_one_of_lt' (by change k + 1 < r + 1; omega)]
        rw [hs, ← Fin.last_sub, ← Fin.last_sub]
        abel
  refine ⟨jf.val, jf.is_lt, ?_⟩
  rw [ntBeta_eq_cycle_rev jf.is_lt]
  apply Equiv.Perm.ext
  intro i
  rw [hform i.val i.is_lt]
  simp only [Equiv.Perm.mul_apply, finCycle_apply, Fin.revPerm_apply]

end MetaMathlibExt
