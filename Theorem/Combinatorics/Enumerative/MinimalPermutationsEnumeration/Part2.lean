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
import Def.Combinatorics.Enumerative.MinimalPermutationsEnumeration


section

namespace MetaMathlibExt

theorem prevPos_val (d : ℕ) (a : Fin (d + 1)) (h : 0 < a.val) :
    (prevPos d a h).val = a.val - 1 := rfl

theorem nextPos_val (d : ℕ) (a : Fin (d + 1)) (h : a.val < d) :
    (nextPos d a h).val = a.val + 2 := rfl

theorem left_bridge_eq (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
    ∃ i : Fin d, (a.castSucc.succAbove i.castSucc).val = a.val - 1 ∧
      (a.castSucc.succAbove i.succ).val = a.val + 1 ∧
      a.castSucc.succAbove i.castSucc = prevPos d a hpos ∧
      a.castSucc.succAbove i.succ = a.succ := by
  have hlt : a.val - 1 < d := by
    have ha := a.isLt
    omega
  let i : Fin d := ⟨a.val - 1, hlt⟩
  have hi : i.val = a.val - 1 := rfl
  have hbridge : i.val + 1 = (a.castSucc : Fin (d + 2)).val := by
    simp only [Fin.val_castSucc, hi]
    omega
  have hb := deletion_bridge_of_eq d a.castSucc i hbridge
  have hx : (a.castSucc.succAbove i.castSucc).val = a.val - 1 := by
    have h1 := hb.1
    simp only [Fin.val_castSucc] at h1
    omega
  have hy : (a.castSucc.succAbove i.succ).val = a.val + 1 := by
    have h2 := hb.2
    omega
  have hxeq : a.castSucc.succAbove i.castSucc = prevPos d a hpos := by
    apply Fin.ext
    simp only [prevPos_val]
    exact hx
  have hyeq : a.castSucc.succAbove i.succ = a.succ := by
    apply Fin.ext
    simp only [Fin.val_succ]
    exact hy
  exact ⟨i, hx, hy, hxeq, hyeq⟩

theorem right_bridge_eq (d : ℕ) (a : Fin (d + 1)) (hlt : a.val < d) :
    ∃ i : Fin d, (a.succ.succAbove i.castSucc).val = a.val ∧
      (a.succ.succAbove i.succ).val = a.val + 2 ∧
      a.succ.succAbove i.castSucc = a.castSucc ∧
      a.succ.succAbove i.succ = nextPos d a hlt := by
  let i : Fin d := ⟨a.val, hlt⟩
  have hi : i.val = a.val := rfl
  have hbridge : i.val + 1 = (a.succ : Fin (d + 2)).val := by
    simp only [Fin.val_succ, hi]
  have hb := deletion_bridge_of_eq d a.succ i hbridge
  have hx : (a.succ.succAbove i.castSucc).val = a.val := by
    have h1 := hb.1
    simp only [Fin.val_succ] at h1
    omega
  have hy : (a.succ.succAbove i.succ).val = a.val + 2 := by
    have h2 := hb.2
    omega
  have hxeq : a.succ.succAbove i.castSucc = a.castSucc := by
    apply Fin.ext
    simp only [Fin.val_castSucc]
    exact hx
  have hyeq : a.succ.succAbove i.succ = nextPos d a hlt := by
    apply Fin.ext
    simp only [nextPos_val]
    exact hy
  exact ⟨i, hx, hy, hxeq, hyeq⟩

theorem left_bridge_ascent_of_minimal (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (hpos : 0 < a.val)
    (hmin : ∀ j : Fin (d + 2), (Finset.univ.filter fun i : Fin d =>
      σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)).card < d) :
    σ (prevPos d a hpos) < σ a.succ := by
  have hcard := hmin a.castSucc
  have hadd := deletion_add d σ a.castSucc
  have hpos2 : 0 < (Finset.univ.filter fun k : Fin d =>
      σ (a.castSucc.succAbove k.castSucc) <
        σ (a.castSucc.succAbove k.succ)).card := by omega
  obtain ⟨i0, hmem⟩ := Finset.card_pos.mp hpos2
  have hasc0 : σ (a.castSucc.succAbove i0.castSucc) <
      σ (a.castSucc.succAbove i0.succ) :=
    (Finset.mem_filter.mp hmem).2
  by_cases heq : i0.val + 1 = (a.castSucc : Fin (d + 2)).val
  · have hb := deletion_bridge_of_eq d a.castSucc i0 heq
    have hx : (a.castSucc.succAbove i0.castSucc).val = a.val - 1 := by
      have h1 := hb.1
      simp only [Fin.val_castSucc] at h1
      omega
    have hy : (a.castSucc.succAbove i0.succ).val = a.val + 1 := by
      have h2 := hb.2
      omega
    have hxeq : a.castSucc.succAbove i0.castSucc = prevPos d a hpos := by
      apply Fin.ext
      simp only [prevPos_val]
      exact hx
    have hyeq : a.castSucc.succAbove i0.succ = a.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      exact hy
    rw [hxeq, hyeq] at hasc0
    exact hasc0
  · obtain ⟨k, hxeq, hyeq⟩ := deletion_consec_of_ne d a.castSucc i0 heq
    have hkne : k ≠ a := by
      intro he
      have hxeq2 : Fin.succAbove a.castSucc i0.castSucc = a.castSucc := by
        rw [hxeq, he]
      exact Fin.succAbove_ne a.castSucc i0.castSucc hxeq2
    have hdesc := descent_of_ne_ascent d σ a k ha hkne
    rw [hxeq, hyeq] at hasc0
    have hlt2 : σ k.castSucc < σ k.succ := hasc0
    have hgt : σ k.succ < σ k.castSucc := hdesc
    exact absurd (lt_trans hlt2 hgt) (lt_irrefl _)

theorem right_bridge_ascent_of_minimal (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (hlt : a.val < d)
    (hmin : ∀ j : Fin (d + 2), (Finset.univ.filter fun i : Fin d =>
      σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)).card < d) :
    σ a.castSucc < σ (nextPos d a hlt) := by
  have hcard := hmin a.succ
  have hadd := deletion_add d σ a.succ
  have hpos2 : 0 < (Finset.univ.filter fun k : Fin d =>
      σ (a.succ.succAbove k.castSucc) <
        σ (a.succ.succAbove k.succ)).card := by omega
  obtain ⟨i0, hmem⟩ := Finset.card_pos.mp hpos2
  have hasc0 : σ (a.succ.succAbove i0.castSucc) <
      σ (a.succ.succAbove i0.succ) :=
    (Finset.mem_filter.mp hmem).2
  by_cases heq : i0.val + 1 = (a.succ : Fin (d + 2)).val
  · have hb := deletion_bridge_of_eq d a.succ i0 heq
    have hx : (a.succ.succAbove i0.castSucc).val = a.val := by
      have h1 := hb.1
      simp only [Fin.val_succ] at h1
      omega
    have hy : (a.succ.succAbove i0.succ).val = a.val + 2 := by
      have h2 := hb.2
      omega
    have hxeq : a.succ.succAbove i0.castSucc = a.castSucc := by
      apply Fin.ext
      simp only [Fin.val_castSucc]
      exact hx
    have hyeq : a.succ.succAbove i0.succ = nextPos d a hlt := by
      apply Fin.ext
      simp only [nextPos_val]
      exact hy
    rw [hxeq, hyeq] at hasc0
    exact hasc0
  · obtain ⟨k, hxeq, hyeq⟩ := deletion_consec_of_ne d a.succ i0 heq
    have hkne : k ≠ a := by
      intro he
      have hyeq2 : Fin.succAbove a.succ i0.succ = a.succ := by
        rw [hyeq, he]
      exact Fin.succAbove_ne a.succ i0.succ hyeq2
    have hdesc := descent_of_ne_ascent d σ a k ha hkne
    rw [hxeq, hyeq] at hasc0
    have hlt2 : σ k.castSucc < σ k.succ := hasc0
    have hgt : σ k.succ < σ k.castSucc := hdesc
    exact absurd (lt_trans hlt2 hgt) (lt_irrefl _)

theorem minimal_of_bridges (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a})
    (hpos : 0 < a.val) (hlt : a.val < d)
    (hleft : σ (prevPos d a hpos) < σ a.succ)
    (hright : σ a.castSucc < σ (nextPos d a hlt)) :
    ∀ j : Fin (d + 2), (Finset.univ.filter fun i : Fin d =>
      σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)).card < d := by
  intro j
  by_cases hj1 : j = a.castSucc
  · subst hj1
    obtain ⟨i, _, _, hxeq, hyeq⟩ := left_bridge_eq d a hpos
    have hasc : σ (a.castSucc.succAbove i.castSucc) <
        σ (a.castSucc.succAbove i.succ) := by
      rw [hxeq, hyeq]
      exact hleft
    exact deletion_card_lt_of_ascent d σ a.castSucc i hasc
  · by_cases hj2 : j = a.succ
    · subst hj2
      obtain ⟨i, _, _, hxeq, hyeq⟩ := right_bridge_eq d a hlt
      have hasc : σ (a.succ.succAbove i.castSucc) <
          σ (a.succ.succAbove i.succ) := by
        rw [hxeq, hyeq]
        exact hright
      exact deletion_card_lt_of_ascent d σ a.succ i hasc
    · obtain ⟨i, hasc⟩ := deletion_ascent_of_ne d σ a j ha hj1 hj2
      exact deletion_card_lt_of_ascent d σ j i hasc

end MetaMathlibExt
end
