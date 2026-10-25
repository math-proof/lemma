/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeshPatternStirlingRecursion.lean -/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.MeshPatternStirlingRecursion.Part3


section

namespace MetaMathlibExt

/-- The shifted max position maximizes `Phi`. -/
lemma Phi_max (m : ℕ) (p : Fin (m.succ)) (τ : Equiv.Perm (Fin m))
    (M' : Fin m) (hM' : ∀ t : Fin m, τ t ≤ τ M') :
    ∀ x : Fin (m.succ), Phi m p τ x ≤ Phi m p τ (p.succAbove M') := by
  intro x
  by_cases hxp : x = p
  · subst hxp
    rw [Phi_apply_p]
    exact Fin.zero_le _
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hxp
    have e1 : Phi m p τ x = (τ j).succ := by
      rw [← hj]
      exact Phi_apply_succAbove m p τ j
    have e2 : Phi m p τ (p.succAbove M') = (τ M').succ :=
      Phi_apply_succAbove m p τ M'
    rw [e1, e2]
    exact Fin.succ_le_succ_iff.mpr (hM' j)

/-- Left-to-right maximality at the insertion point holds iff it is at the front. -/
lemma Phi_ltr_p (m : ℕ) (p : Fin (m.succ)) (τ : Equiv.Perm (Fin m)) :
    (∀ t : Fin (m.succ), t < p → Phi m p τ t < Phi m p τ p) ↔ p = 0 := by
  constructor
  · intro h
    by_contra hne
    have h0lt : (0 : Fin (m.succ)) < p := by
      by_contra hcon
      rw [not_lt] at hcon
      exact hne (le_antisymm hcon (Fin.zero_le p))
    have hbad := h 0 h0lt
    rw [Phi_apply_p] at hbad
    exact absurd hbad (not_lt_of_ge (Fin.zero_le _))
  · intro hp t ht
    subst hp
    exact absurd ht (Fin.not_lt_zero t)

/-- Left-to-right maximality transfers across the insertion. -/
lemma Phi_ltr_succAbove (m : ℕ) (p : Fin (m.succ)) (τ : Equiv.Perm (Fin m))
    (j : Fin m) :
    (∀ t : Fin (m.succ), t < p.succAbove j → Phi m p τ t < Phi m p τ (p.succAbove j))
    ↔ (∀ i : Fin m, i < j → τ i < τ j) := by
  constructor
  · intro h i hij
    have hlt : p.succAbove i < p.succAbove j :=
      Fin.succAbove_lt_succAbove_iff.mpr hij
    have h2 := h _ hlt
    rw [Phi_apply_succAbove, Phi_apply_succAbove] at h2
    exact Fin.succ_lt_succ_iff.mp h2
  · intro h t ht
    by_cases htp : t = p
    · subst htp
      rw [Phi_apply_p, Phi_apply_succAbove]
      exact Fin.succ_pos _
    · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq htp
      have hij : i < j := by
        have hrew : p.succAbove i < p.succAbove j := by
          rw [hi]
          exact ht
        exact Fin.succAbove_lt_succAbove_iff.mp hrew
      have h2 := h i hij
      have e1 : Phi m p τ t = (τ i).succ := by
        rw [← hi]
        exact Phi_apply_succAbove m p τ i
      have e2 : Phi m p τ (p.succAbove j) = (τ j).succ :=
        Phi_apply_succAbove m p τ j
      rw [e1, e2]
      exact Fin.succ_lt_succ_iff.mpr h2

/-- The witness filter at a shifted position has the same card as for `τ`. -/
lemma Phi_filter_card (m : ℕ) (p : Fin (m.succ)) (τ : Equiv.Perm (Fin m))
    (M' : Fin m) (j : Fin m) :
    (Finset.univ.filter (fun i : Fin m =>
      j < i ∧ i < M' ∧ τ j < τ i)).card
    = (Finset.univ.filter (fun t : Fin (m.succ) =>
      p.succAbove j < t ∧ t < p.succAbove M' ∧
        Phi m p τ (p.succAbove j) < Phi m p τ t)).card := by
  apply Finset.card_bij (fun i _ => p.succAbove i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    obtain ⟨hij, hiM, hτ⟩ := hi
    refine ⟨Fin.succAbove_lt_succAbove_iff.mpr hij,
      Fin.succAbove_lt_succAbove_iff.mpr hiM, ?_⟩
    rw [Phi_apply_succAbove, Phi_apply_succAbove]
    exact Fin.succ_lt_succ_iff.mpr hτ
  · intro a₁ _ a₂ _ heq
    exact Fin.succAbove_right_injective heq
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    obtain ⟨hjt, htM, hστ⟩ := ht
    have htp : t ≠ p := by
      intro hcon
      subst hcon
      rw [Phi_apply_p, Phi_apply_succAbove] at hστ
      exact absurd hστ (not_lt_of_ge (Fin.zero_le _))
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq htp
    have hmem : i ∈ Finset.univ.filter (fun i : Fin m =>
        j < i ∧ i < M' ∧ τ j < τ i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hjt' : j < i := by
        have hrew : p.succAbove j < p.succAbove i := by
          rw [hi]
          exact hjt
        exact Fin.succAbove_lt_succAbove_iff.mp hrew
      have htM' : i < M' := by
        have hrew : p.succAbove i < p.succAbove M' := by
          rw [hi]
          exact htM
        exact Fin.succAbove_lt_succAbove_iff.mp hrew
      have hτ' : τ j < τ i := by
        have hrew : Phi m p τ (p.succAbove j) < Phi m p τ (p.succAbove i) := by
          rw [hi]
          exact hστ
        rw [Phi_apply_succAbove, Phi_apply_succAbove] at hrew
        exact Fin.succ_lt_succ_iff.mp hrew
      exact ⟨hjt', htM', hτ'⟩
    exact ⟨i, hmem, hi⟩

/-- The witness filter at a fresh front position counts the earlier-max positions. -/
lemma Phi_filter_p0 (m : ℕ) (τ : Equiv.Perm (Fin m)) (M' : Fin m) :
    (Finset.univ.filter (fun t : Fin (m.succ) =>
      (0 : Fin (m.succ)) < t ∧ t < (0 : Fin (m.succ)).succAbove M' ∧
        Phi m 0 τ 0 < Phi m 0 τ t)).card = M'.val := by
  have hM : (0 : Fin (m.succ)).succAbove M' = M'.succ := Fin.zero_succAbove M'
  have hσ0 : Phi m 0 τ 0 = 0 := Phi_apply_p m 0 τ
  rw [hM]
  have hset : Finset.univ.filter (fun t : Fin (m.succ) =>
      (0 : Fin (m.succ)) < t ∧ t < M'.succ ∧ Phi m 0 τ 0 < Phi m 0 τ t)
      = (Finset.Iio M'.succ).erase 0 := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
      Finset.mem_Iio]
    constructor
    · rintro ⟨h0t, htM, hσ⟩
      refine ⟨?_, htM⟩
      intro hcon
      subst hcon
      rw [hσ0] at hσ
      exact absurd hσ (lt_irrefl _)
    · rintro ⟨hne, htM⟩
      refine ⟨?_, htM, ?_⟩
      · rwa [Fin.pos_iff_ne_zero]
      · rw [hσ0]
        by_contra hcon
        push Not at hcon
        have h0 := le_antisymm hcon (Fin.zero_le _)
        have hpre := Phi_preimage_zero m 0 τ t h0
        exact hne hpre
  rw [hset, Finset.card_erase_of_mem]
  · rw [Fin.card_Iio]
    simp [Fin.val_succ]
  · simp [Fin.succ_pos]

end MetaMathlibExt
end
