/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fin.Rev
import Mathlib.Order.Fin.Basic


section

namespace MetaMathlibExt

theorem descent_or_ascent (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) (i : Fin (d + 1)) :
    (σ i.castSucc > σ i.succ) ∨ (σ i.castSucc < σ i.succ) := by
  have hne : (i.castSucc : Fin (d + 2)) ≠ i.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp [Fin.val_castSucc, Fin.val_succ] at hv
  have h : σ i.castSucc ≠ σ i.succ := fun he => hne (σ.injective he)
  rcases lt_or_gt_of_ne h with h1 | h1
  · exact Or.inr h1
  · exact Or.inl h1

theorem descent_add_ascent (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) :
    (Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc > σ i.succ).card +
    (Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc < σ i.succ).card = d + 1 := by
  have hunion : (Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc > σ i.succ) ∪
    (Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc < σ i.succ) = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_of_true (descent_or_ascent d σ i) trivial
  have hdisj : Disjoint
    (Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc > σ i.succ)
    (Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc < σ i.succ) := by
    apply Finset.disjoint_filter.mpr
    intro i _ h1 h2
    exact absurd (lt_trans h2 h1) (lt_irrefl _)
  calc (Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc > σ i.succ).card +
      (Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc < σ i.succ).card
      = ((Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc > σ i.succ) ∪
        (Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc < σ i.succ)).card := by
          rw [Finset.card_union_of_disjoint hdisj]
    _ = Finset.univ.card := by rw [hunion]
    _ = d + 1 := by simp

-- Permutations with `d` descents have exactly one ascent.
theorem exactly_one_ascent_of_descent_eq (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (h : (Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc > σ i.succ).card = d) :
    (Finset.univ.filter fun i : Fin (d + 1) => σ i.castSucc < σ i.succ).card = 1 := by
  have h2 := descent_add_ascent d σ
  omega

theorem deletion_gap_ne (d : ℕ) (j : Fin (d + 2)) (i : Fin d) :
    j.succAbove i.castSucc ≠ j.succAbove i.succ := by
  apply Fin.succAbove_right_injective.ne
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castSucc, Fin.val_succ] at hv
  omega

theorem deletion_or (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) (j : Fin (d + 2))
    (i : Fin d) :
    (σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)) ∨
      (σ (j.succAbove i.castSucc) < σ (j.succAbove i.succ)) := by
  have hne : σ (j.succAbove i.castSucc) ≠ σ (j.succAbove i.succ) :=
    fun he => deletion_gap_ne d j i (σ.injective he)
  rcases lt_or_gt_of_ne hne with h1 | h1
  · exact Or.inr h1
  · exact Or.inl h1

theorem deletion_add (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) (j : Fin (d + 2)) :
    (Finset.univ.filter fun i : Fin d =>
        σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)).card +
      (Finset.univ.filter fun i : Fin d =>
        σ (j.succAbove i.castSucc) < σ (j.succAbove i.succ)).card = d := by
  have hunion : (Finset.univ.filter fun i : Fin d =>
        σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)) ∪
      (Finset.univ.filter fun i : Fin d =>
        σ (j.succAbove i.castSucc) < σ (j.succAbove i.succ)) = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_of_true (deletion_or d σ j i) trivial
  have hdisj : Disjoint
      (Finset.univ.filter fun i : Fin d =>
        σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ))
      (Finset.univ.filter fun i : Fin d =>
        σ (j.succAbove i.castSucc) < σ (j.succAbove i.succ)) := by
    apply Finset.disjoint_filter.mpr
    intro i _ h1 h2
    exact absurd (lt_trans h2 h1) (lt_irrefl _)
  calc (Finset.univ.filter fun i : Fin d =>
          σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)).card +
        (Finset.univ.filter fun i : Fin d =>
          σ (j.succAbove i.castSucc) < σ (j.succAbove i.succ)).card
      = ((Finset.univ.filter fun i : Fin d =>
            σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)) ∪
          (Finset.univ.filter fun i : Fin d =>
            σ (j.succAbove i.castSucc) < σ (j.succAbove i.succ))).card := by
          rw [Finset.card_union_of_disjoint hdisj]
    _ = Finset.univ.card := by rw [hunion]
    _ = d := by simp

theorem succAbove_val (d : ℕ) (j : Fin (d + 2)) (k : Fin (d + 1)) :
    (j.succAbove k).val = if k.val < j.val then k.val else k.val + 1 := by
  by_cases h : k.val < j.val
  · have hc : k.castSucc < j := by
      rw [Fin.lt_def]
      simp only [Fin.val_castSucc]
      exact h
    rw [Fin.succAbove_of_castSucc_lt _ _ hc]
    simp only [Fin.val_castSucc, h, ↓reduceIte]
  · have hc : ¬ k.castSucc < j := by
      rw [Fin.lt_def]
      simp only [Fin.val_castSucc]
      exact h
    rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hc)]
    simp only [Fin.val_succ, h, ↓reduceIte]

theorem deletion_consec_of_ne (d : ℕ) (j : Fin (d + 2)) (i : Fin d)
    (h : i.val + 1 ≠ j.val) :
    ∃ k : Fin (d + 1), j.succAbove i.castSucc = k.castSucc ∧
      j.succAbove i.succ = k.succ := by
  have hx : (j.succAbove i.castSucc).val =
      if i.val < j.val then i.val else i.val + 1 := by
    have hv := succAbove_val d j i.castSucc
    simp only [Fin.val_castSucc] at hv
    exact hv
  have hy : (j.succAbove i.succ).val =
      if i.val + 1 < j.val then i.val + 1 else i.val + 2 := by
    have hv := succAbove_val d j i.succ
    simp only [Fin.val_succ] at hv
    exact hv
  have hcases : (j.succAbove i.castSucc).val + 1 = (j.succAbove i.succ).val := by
    by_cases hlt : i.val + 1 < j.val
    · have h1 : i.val < j.val := by omega
      simp only [hx, hy, h1, hlt, ↓reduceIte]
    · have hle : j.val ≤ i.val := by omega
      have h1 : ¬ i.val < j.val := by omega
      have h2 : ¬ i.val + 1 < j.val := hlt
      simp only [hx, hy, h1, h2, ↓reduceIte]
  have hlt : (j.succAbove i.castSucc).val < d + 1 := by
    have hj := (j.succAbove i.succ).isLt
    omega
  let k : Fin (d + 1) := ⟨(j.succAbove i.castSucc).val, hlt⟩
  have hk1 : (k.castSucc).val = (j.succAbove i.castSucc).val := by
    simp only [Fin.val_castSucc, k]
  have hk2 : (k.succ).val = (j.succAbove i.succ).val := by
    simp only [Fin.val_succ, k]
    omega
  refine ⟨k, ?_, ?_⟩
  · exact Fin.ext hk1.symm
  · exact Fin.ext hk2.symm

theorem deletion_bridge_of_eq (d : ℕ) (j : Fin (d + 2)) (i : Fin d)
    (h : i.val + 1 = j.val) :
    (j.succAbove i.castSucc).val + 1 = j.val ∧
      (j.succAbove i.succ).val = (j.succAbove i.castSucc).val + 2 := by
  have hx : (j.succAbove i.castSucc).val =
      if i.val < j.val then i.val else i.val + 1 := by
    have hv := succAbove_val d j i.castSucc
    simp only [Fin.val_castSucc] at hv
    exact hv
  have hy : (j.succAbove i.succ).val =
      if i.val + 1 < j.val then i.val + 1 else i.val + 2 := by
    have hv := succAbove_val d j i.succ
    simp only [Fin.val_succ] at hv
    exact hv
  have h1 : i.val < j.val := by omega
  have h2 : ¬ i.val + 1 < j.val := by omega
  rw [hx, hy, ite_eq_left h1, ite_eq_right h2]
  constructor
  · omega
  · rfl

theorem ascent_singleton_of_descent (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (h : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc > σ i.succ).card = d) :
    ∃ a : Fin (d + 1), (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a} := by
  have h1 := exactly_one_ascent_of_descent_eq d σ h
  exact Finset.card_eq_one.mp h1

theorem descent_of_ne_ascent (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a k : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a}) (hk : k ≠ a) :
    σ k.castSucc > σ k.succ := by
  have hmem : k ∉ Finset.univ.filter (fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) := by
    rw [ha]
    exact fun h => hk (Finset.mem_singleton.mp h)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hmem
  have hne : σ k.castSucc ≠ σ k.succ := by
    have hkk : (k.castSucc : Fin (d + 2)) ≠ k.succ := by
      intro hh
      have hv := congrArg Fin.val hh
      simp only [Fin.val_castSucc, Fin.val_succ] at hv
      omega
    exact fun he => hkk (σ.injective he)
  have hle : σ k.succ ≤ σ k.castSucc := hmem
  have hlt : σ k.succ < σ k.castSucc := lt_of_le_of_ne hle (Ne.symm hne)
  exact hlt

theorem deletion_ascent_of_ne (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1)) (j : Fin (d + 2))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (hj1 : j ≠ a.castSucc) (hj2 : j ≠ a.succ) :
    ∃ i : Fin d, σ (j.succAbove i.castSucc) < σ (j.succAbove i.succ) := by
  have hasc := ascent_of_mem_singleton d σ a ha
  have hj1' : j.val ≠ a.val := by
    intro he
    apply hj1
    apply Fin.ext
    simp only [Fin.val_castSucc]
    exact he
  have hj2' : j.val ≠ a.val + 1 := by
    intro he
    apply hj2
    apply Fin.ext
    simp only [Fin.val_succ]
    exact he
  by_cases hlt : a.val + 1 < j.val
  · have hlt1 : a.val < d := by
      have hj := j.isLt
      omega
    let i : Fin d := ⟨a.val, hlt1⟩
    have hi1 : i.val = a.val := rfl
    have hx : (j.succAbove i.castSucc).val = a.val := by
      have hv := succAbove_val d j i.castSucc
      simp only [Fin.val_castSucc, hi1] at hv
      have h1 : i.val < j.val := by omega
      rw [hv, ite_eq_left h1]
    have hy : (j.succAbove i.succ).val = a.val + 1 := by
      have hv := succAbove_val d j i.succ
      simp only [Fin.val_succ, hi1] at hv
      have h2 : i.val + 1 < j.val := by omega
      rw [hv, ite_eq_left h2]
    have hxeq : j.succAbove i.castSucc = a.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      exact hx
    have hyeq : j.succAbove i.succ = a.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      exact hy
    exact ⟨i, by rw [hxeq, hyeq]; exact hasc⟩
  · have hle : j.val ≤ a.val + 1 := by omega
    have hle2 : j.val ≤ a.val := by omega
    have hlt2 : j.val < a.val := by
      have := hj1'
      omega
    have hpos : 1 ≤ a.val := by omega
    have hlt3 : a.val - 1 < d := by
      have ha2 := a.isLt
      omega
    let i : Fin d := ⟨a.val - 1, hlt3⟩
    have hi1 : i.val = a.val - 1 := rfl
    have hsucc : i.val + 1 = a.val := by omega
    have hx : (j.succAbove i.castSucc).val = a.val := by
      have hv := succAbove_val d j i.castSucc
      simp only [Fin.val_castSucc, hi1] at hv
      have h1 : ¬ i.val < j.val := by omega
      rw [hv, ite_eq_right h1]
      omega
    have hy : (j.succAbove i.succ).val = a.val + 1 := by
      have hv := succAbove_val d j i.succ
      simp only [Fin.val_succ, hi1] at hv
      have h2 : ¬ i.val + 1 < j.val := by omega
      rw [hv, ite_eq_right h2]
      have h3 : (i.succ).val = a.val := by
        simp only [Fin.val_succ, hi1]
        omega
      omega
    have hxeq : j.succAbove i.castSucc = a.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      exact hx
    have hyeq : j.succAbove i.succ = a.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      exact hy
    exact ⟨i, by rw [hxeq, hyeq]; exact hasc⟩

theorem deletion_card_lt_of_ascent (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (j : Fin (d + 2)) (i : Fin d)
    (h : σ (j.succAbove i.castSucc) < σ (j.succAbove i.succ)) :
    (Finset.univ.filter fun k : Fin d =>
      σ (j.succAbove k.castSucc) > σ (j.succAbove k.succ)).card < d := by
  have hadd := deletion_add d σ j
  have hmem : i ∈ Finset.univ.filter (fun k : Fin d =>
      σ (j.succAbove k.castSucc) < σ (j.succAbove k.succ)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  have hpos : 0 < (Finset.univ.filter fun k : Fin d =>
      σ (j.succAbove k.castSucc) < σ (j.succAbove k.succ)).card :=
    Finset.card_pos.mpr ⟨i, hmem⟩
  omega

theorem deletion_card_eq_of_all_descents (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (j : Fin (d + 2))
    (h : ∀ i : Fin d, σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)) :
    (Finset.univ.filter fun k : Fin d =>
      σ (j.succAbove k.castSucc) > σ (j.succAbove k.succ)).card = d := by
  have hfun : (Finset.univ.filter fun k : Fin d =>
      σ (j.succAbove k.castSucc) > σ (j.succAbove k.succ)) = Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact h i
  rw [hfun]
  simp

theorem end_first_not_minimal (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a}) (hav : a.val = 0) :
    (Finset.univ.filter fun i : Fin d =>
      σ ((0 : Fin (d + 2)).succAbove i.castSucc) >
        σ ((0 : Fin (d + 2)).succAbove i.succ)).card = d := by
  apply deletion_card_eq_of_all_descents
  intro i
  have hne : i.val + 1 ≠ (0 : Fin (d + 2)).val := by
    simp only [Fin.val_zero]
    omega
  obtain ⟨k, hxeq, hyeq⟩ := deletion_consec_of_ne d 0 i hne
  have hkne : k ≠ a := by
    intro he
    subst he
    have hvk : k.val = ((0 : Fin (d + 2)).succAbove i.castSucc).val := by
      rw [hxeq]
      simp only [Fin.val_castSucc]
    have hx : ((0 : Fin (d + 2)).succAbove i.castSucc).val = i.val + 1 := by
      have hv := succAbove_val d 0 i.castSucc
      simp only [Fin.val_castSucc, Fin.val_zero] at hv
      have h1 : ¬ i.val < 0 := by omega
      simp only [hv, h1, ↓reduceIte]
    omega
  have hdesc := descent_of_ne_ascent d σ a k ha hkne
  rw [hxeq, hyeq]
  exact hdesc

theorem end_last_not_minimal (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a}) (hav : a.val = d) :
    (Finset.univ.filter fun i : Fin d =>
      σ ((Fin.last (d + 1)).succAbove i.castSucc) >
        σ ((Fin.last (d + 1)).succAbove i.succ)).card = d := by
  apply deletion_card_eq_of_all_descents
  intro i
  have hlast : (Fin.last (d + 1)).val = d + 1 := rfl
  have hne : i.val + 1 ≠ (Fin.last (d + 1)).val := by
    have hi := i.isLt
    omega
  obtain ⟨k, hxeq, hyeq⟩ :=
    deletion_consec_of_ne d (Fin.last (d + 1)) i hne
  have hkne : k ≠ a := by
    intro he
    subst he
    have hvk : k.val = ((Fin.last (d + 1)).succAbove i.castSucc).val := by
      rw [hxeq]
      simp only [Fin.val_castSucc]
    have hx : ((Fin.last (d + 1)).succAbove i.castSucc).val = i.val := by
      have hv := succAbove_val d (Fin.last (d + 1)) i.castSucc
      simp only [Fin.val_castSucc] at hv
      have h1 : i.val < (Fin.last (d + 1)).val := by
        have hi := i.isLt
        have hl := (Fin.last (d + 1)).isLt
        omega
      simp only [hv, h1, ↓reduceIte]
    omega
  have hdesc := descent_of_ne_ascent d σ a k ha hkne
  rw [hxeq, hyeq]
  exact hdesc

end MetaMathlibExt
end
