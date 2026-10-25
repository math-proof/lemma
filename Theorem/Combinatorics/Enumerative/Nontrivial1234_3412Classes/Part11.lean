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
import Def.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part11


namespace MetaMathlibExt

lemma ntDSemi_pair_mem {m : ℕ} (hm : 0 < m)
    {α : Equiv.Perm (Fin (m + 1))} (hα : ¬ntSemi α)
    {y : Fin (m + 1)} (hy : y ∈ ntDSemi α) :
    (finRotate (m + 1)).symm y ∈ ntBreaks α ∧ y ∈ ntBreaks α := by
  obtain ⟨ρ, hαρ, hρ⟩ := (nt_mem_DSemi_iff α y).1 hy
  have hρempty : ntBreaks ρ = ∅ :=
    (ntSemi_iff_breaks_empty hm ρ).1 hρ
  have hinsnot : ¬ntSemi (ntIns y (α y) ρ) := by
    rwa [← hαρ]
  have hbreaks := ntBreaks_ins_eq_triple hm y (α y) ρ hρempty hinsnot
  rw [← hαρ] at hbreaks
  rw [hbreaks]
  simp

lemma ntBreaks_card_eq_three_of_mem_DSemi {m : ℕ} (hm : 0 < m)
    {α : Equiv.Perm (Fin (m + 1))} (hα : ¬ntSemi α)
    {y : Fin (m + 1)} (hy : y ∈ ntDSemi α) : (ntBreaks α).card = 3 := by
  obtain ⟨ρ, hαρ, hρ⟩ := (nt_mem_DSemi_iff α y).1 hy
  have hρempty : ntBreaks ρ = ∅ := (ntSemi_iff_breaks_empty hm ρ).1 hρ
  have hsub : ntBreaks α ⊆
      {(finRotate (m + 1)).symm y, y,
        α.symm (finRotate (m + 1) (α y))} := by
    rw [hαρ]
    simpa only [ntIns_apply_same] using
      ntBreaks_ins_subset hm y (α y) ρ hρempty
  have htriple :
      ({(finRotate (m + 1)).symm y, y,
        α.symm (finRotate (m + 1) (α y))} : Finset (Fin (m + 1))).card ≤ 3 := by
    have hA := Finset.card_insert_le ((finRotate (m + 1)).symm y)
      ({y, α.symm (finRotate (m + 1) (α y))} : Finset (Fin (m + 1)))
    have hB := Finset.card_insert_le y
      ({α.symm (finRotate (m + 1) (α y))} : Finset (Fin (m + 1)))
    have hC : ({α.symm (finRotate (m + 1) (α y))} :
        Finset (Fin (m + 1))).card = 1 := by simp
    omega
  have hle : (ntBreaks α).card ≤ 3 := by
    calc
      (ntBreaks α).card ≤
          ({(finRotate (m + 1)).symm y, y,
            α.symm (finRotate (m + 1) (α y))} : Finset (Fin (m + 1))).card :=
        Finset.card_le_card hsub
      _ ≤ 3 := htriple
  have hne0 : (ntBreaks α).card ≠ 0 := by
    intro h
    apply hα
    rw [ntSemi_iff_breaks_empty (by omega)]
    exact Finset.card_eq_zero.mp h
  have hne1 := nt_card_breaks_ne_one α
  have hne2 := nt_card_breaks_ne_two α
  omega

lemma ntDSemi_card_le_two {m : ℕ} (hm : 3 ≤ m)
    {α : Equiv.Perm (Fin (m + 1))} (hα : ¬ntSemi α) :
    (ntDSemi α).card ≤ 2 := by
  classical
  by_contra hle
  have hlt : 2 < (ntDSemi α).card := by omega
  obtain ⟨y₁, y₂, y₃, hy₁, hy₂, hy₃, hy₁₂, hy₁₃, hy₂₃⟩ :=
    Finset.two_lt_card_iff.mp hlt
  obtain ⟨ρ, hαρ, hρ⟩ := (nt_mem_DSemi_iff α y₁).1 hy₁
  have hρempty : ntBreaks ρ = ∅ :=
    (ntSemi_iff_breaks_empty (by omega) ρ).1 hρ
  have hinsnot : ¬ntSemi (ntIns y₁ (α y₁) ρ) := by
    rwa [← hαρ]
  have hbreaks :=
    ntBreaks_ins_eq_triple (by omega) y₁ (α y₁) ρ hρempty hinsnot
  rw [← hαρ] at hbreaks
  have hy₂pair := ntDSemi_pair_mem (by omega) hα hy₂
  have hy₃pair := ntDSemi_pair_mem (by omega) hα hy₃
  have hy₂cases :
      y₂ = (finRotate (m + 1)).symm y₁ ∨ y₂ = y₁ ∨
        y₂ = α.symm (finRotate (m + 1) (α y₁)) := by
    rw [hbreaks] at hy₂pair
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hy₂pair.2
  have hy₃cases :
      y₃ = (finRotate (m + 1)).symm y₁ ∨ y₃ = y₁ ∨
        y₃ = α.symm (finRotate (m + 1) (α y₁)) := by
    rw [hbreaks] at hy₃pair
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hy₃pair.2
  have hy₂two :
      y₂ = (finRotate (m + 1)).symm y₁ ∨
        y₂ = α.symm (finRotate (m + 1) (α y₁)) := by
    rcases hy₂cases with h | h | h
    · exact Or.inl h
    · exact False.elim (hy₁₂ h.symm)
    · exact Or.inr h
  have hy₃two :
      y₃ = (finRotate (m + 1)).symm y₁ ∨
        y₃ = α.symm (finRotate (m + 1) (α y₁)) := by
    rcases hy₃cases with h | h | h
    · exact Or.inl h
    · exact False.elim (hy₁₃ h.symm)
    · exact Or.inr h
  have himpossible
      (hp : (finRotate (m + 1)).symm
          ((finRotate (m + 1)).symm y₁) ∈ ntBreaks α)
      (hs : (finRotate (m + 1)).symm
          (α.symm (finRotate (m + 1) (α y₁))) ∈ ntBreaks α) : False := by
    have hpCases := hp
    rw [hbreaks] at hpCases
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpCases
    have hpPrev : (finRotate (m + 1)).symm
        ((finRotate (m + 1)).symm y₁) ≠
          (finRotate (m + 1)).symm y₁ :=
      ntRotate_symm_ne_self (by omega)
        ((finRotate (m + 1)).symm y₁)
    have hpSelf : (finRotate (m + 1)).symm
        ((finRotate (m + 1)).symm y₁) ≠ y₁ :=
      ntRotate_symm_sq_ne_self (by omega) y₁
    have hcross : (finRotate (m + 1)).symm
        ((finRotate (m + 1)).symm y₁) =
          α.symm (finRotate (m + 1) (α y₁)) := by
      rcases hpCases with h | h | h
      · exact False.elim (hpPrev h)
      · exact False.elim (hpSelf h)
      · exact h
    have hsCases := hs
    rw [hbreaks] at hsCases
    rw [← hcross] at hsCases
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsCases
    have hcPrev : (finRotate (m + 1)).symm
        ((finRotate (m + 1)).symm ((finRotate (m + 1)).symm y₁)) ≠
          (finRotate (m + 1)).symm y₁ := by
      intro h
      apply ntRotate_symm_sq_ne_self (by omega) y₁
      exact (finRotate (m + 1)).symm.injective h
    have hcSelf : (finRotate (m + 1)).symm
        ((finRotate (m + 1)).symm ((finRotate (m + 1)).symm y₁)) ≠ y₁ :=
      ntRotate_symm_cube_ne_self (by omega) y₁
    have hcSq : (finRotate (m + 1)).symm
        ((finRotate (m + 1)).symm ((finRotate (m + 1)).symm y₁)) ≠
          (finRotate (m + 1)).symm ((finRotate (m + 1)).symm y₁) :=
      ntRotate_symm_ne_self (by omega)
        ((finRotate (m + 1)).symm ((finRotate (m + 1)).symm y₁))
    rcases hsCases with h | h | h
    · exact hcPrev h
    · exact hcSelf h
    · exact hcSq h
  rcases hy₂two with h₂ | h₂ <;> rcases hy₃two with h₃ | h₃
  · exact hy₂₃ (h₂.trans h₃.symm)
  · apply himpossible
    · rw [h₂] at hy₂pair
      exact hy₂pair.1
    · rw [h₃] at hy₃pair
      exact hy₃pair.1
  · apply himpossible
    · rw [h₃] at hy₃pair
      exact hy₃pair.1
    · rw [h₂] at hy₂pair
      exact hy₂pair.1
  · exact hy₂₃ (h₂.trans h₃.symm)

end MetaMathlibExt
