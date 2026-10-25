/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexStartPhaseRepair.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryUncond.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexSmallIncidenceEnumeration.Part2


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators


noncomputable def hexSmallCellCoreEnumeration (a : ℂ) (h0 : ℤ) :
    HexFiniteStripCoreIncidenceEnumeration (hexSmallCellBoundaryCore a h0) where
  mid_complete := by
    intro m hm
    change m ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ) at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm | hm
    · subst m
      exact ⟨hexSmallCellIncidence 0, hexSmallCellIncidence_mem a h0 0,
        by simp [hexSmallCellIncidence, hexUncondDomain, hexUncondMid,
          hexConcrete_p_eq]⟩
    · subst m
      exact ⟨hexSmallCellIncidence 1, hexSmallCellIncidence_mem a h0 1, rfl⟩
    · subst m
      exact ⟨hexSmallCellIncidence 2, hexSmallCellIncidence_mem a h0 2, rfl⟩
  boundary_mid_injective := by
    intro e₁ he₁ e₂ he₂ hmid
    rcases e₁ with ⟨v₁, j₁⟩
    rcases e₂ with ⟨v₂, j₂⟩
    fin_cases v₁
    fin_cases v₂
    apply congrArg hexSmallCellIncidence
    apply hexUncondMid_injective a h0
    simpa [hexUncondDomain] using hmid
  boundary_classified := by
    intro e he
    rcases e with ⟨v, j⟩
    fin_cases v
    change hexUncondMid a h0 j = a
      ∨ hexUncondMid a h0 j ∈ (∅ : Set ℂ)
      ∨ hexUncondMid a h0 j ∈ ({hexConcreteQ a h0} : Set ℂ)
      ∨ hexUncondMid a h0 j ∈ (∅ : Set ℂ)
      ∨ hexUncondMid a h0 j ∈ ({hexConcreteR a h0} : Set ℂ)
    fin_cases j
    · exact Or.inl (hexConcrete_p_eq a h0)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  part_unique := by
    intro z hz k l hk hl
    change z ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ) at hz
    change ((k = 0 ∧ z = a) ∨ (k = 1 ∧ z ∈ (∅ : Set ℂ))
      ∨ (k = 2 ∧ z ∈ ({hexConcreteQ a h0} : Set ℂ))
      ∨ (k = 3 ∧ z ∈ (∅ : Set ℂ))
      ∨ (k = 4 ∧ z ∈ ({hexConcreteR a h0} : Set ℂ))) at hk
    change ((l = 0 ∧ z = a) ∨ (l = 1 ∧ z ∈ (∅ : Set ℂ))
      ∨ (l = 2 ∧ z ∈ ({hexConcreteQ a h0} : Set ℂ))
      ∨ (l = 3 ∧ z ∈ (∅ : Set ℂ))
      ∨ (l = 4 ∧ z ∈ ({hexConcreteR a h0} : Set ℂ))) at hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Set.mem_empty_iff_false, and_false, Set.mem_singleton_iff] at hk hl
    rcases hz with hza | hzq | hzr
    · rw [hza] at hk hl
      simp [hexConcrete_a_ne_q a h0, hexConcrete_a_ne_r a h0] at hk hl
      exact hk.trans hl.symm
    · rw [hzq] at hk hl
      simp [(hexConcrete_a_ne_q a h0).symm, hexConcrete_q_ne_r a h0] at hk hl
      exact hk.trans hl.symm
    · rw [hzr] at hk hl
      simp [(hexConcrete_a_ne_r a h0).symm,
        (hexConcrete_q_ne_r a h0).symm] at hk hl
      exact hk.trans hl.symm
  side_complete := by
    intro z hz hpart
    change z ∈ ({a, hexConcreteQ a h0, hexConcreteR a h0} : Finset ℂ) at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz | hz
    · subst z
      exact ⟨hexSmallCellIncidence 0,
        hexSmallCellIncidence_boundary_mem a h0 0,
        by simp [hexSmallCellIncidence, hexUncondDomain, hexUncondMid,
          hexConcrete_p_eq]⟩
    · subst z
      exact ⟨hexSmallCellIncidence 1,
        hexSmallCellIncidence_boundary_mem a h0 1,
        rfl⟩
    · subst z
      exact ⟨hexSmallCellIncidence 2,
        hexSmallCellIncidence_boundary_mem a h0 2,
        rfl⟩


end StatMech.Universality
