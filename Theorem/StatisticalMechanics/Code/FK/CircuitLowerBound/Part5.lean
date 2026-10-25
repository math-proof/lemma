/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CircuitLowerBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Def.StatisticalMechanics.Code.FK.CircuitLowerBound.Part4
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem closedMass_reindex {p q : ℝ} (e : Sym2 V) {γ : Finset (Sym2 V)} (he : e ∉ γ) :
    closedMass G p q γ
      = ∑ ψ ∈ cfib e γ,
          (fkProb G p q (setOpen e ψ) + fkProb G p q (setClosed e ψ)) := by
  classical
  unfold closedMass cfib
  rw [Finset.sum_add_distrib]
  have hclosed : (∑ ψ ∈ Finset.univ.filter
        (fun ψ : ConfigSpace (Sym2 V) => ψ e = false ∧ ∀ e' ∈ γ, ψ e' = false),
        fkProb G p q (setClosed e ψ))
      = ∑ ω ∈ Finset.univ.filter
          (fun ω : ConfigSpace (Sym2 V) => (∀ e' ∈ γ, ω e' = false) ∧ ω e = false),
          fkProb G p q ω := by
    apply Finset.sum_nbij' (fun ψ => ψ) (fun ω => ω)
    · intro ψ hψ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ ⊢
      exact ⟨hψ.2, hψ.1⟩
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      exact ⟨hω.2, hω.1⟩
    · intro ψ _; rfl
    · intro ω _; rfl
    · intro ψ hψ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ
      congr 1
      funext x; by_cases hx : x = e
      · subst hx; simp [hψ.1]
      · rw [setClosed_of_ne hx]
  have hopen : (∑ ψ ∈ Finset.univ.filter
        (fun ψ : ConfigSpace (Sym2 V) => ψ e = false ∧ ∀ e' ∈ γ, ψ e' = false),
        fkProb G p q (setOpen e ψ))
      = ∑ ω ∈ Finset.univ.filter
          (fun ω : ConfigSpace (Sym2 V) => (∀ e' ∈ γ, ω e' = false) ∧ ω e = true),
          fkProb G p q ω := by
    apply Finset.sum_nbij' (fun ψ => setOpen e ψ) (fun ω => setClosed e ω)
    · intro ψ hψ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ ⊢
      refine ⟨fun e' he' => ?_, by simp⟩
      have hne : e' ≠ e := fun h => he (h ▸ he')
      rw [setOpen_of_ne hne]; exact hψ.2 e' he'
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      refine ⟨by simp, fun e' he' => ?_⟩
      have hne : e' ≠ e := fun h => he (h ▸ he')
      rw [setClosed_of_ne hne]; exact hω.1 e' he'
    · intro ψ hψ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ
      funext x; by_cases hx : x = e
      · subst hx; simp [hψ.1]
      · rw [setClosed_of_ne hx, setOpen_of_ne hx]
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      funext x; by_cases hx : x = e
      · subst hx; simp [hω.2]
      · rw [setOpen_of_ne hx, setClosed_of_ne hx]
    · intro ψ _; rfl
  rw [hopen, hclosed]
  have hset1 : (Finset.univ.filter
        (fun ω : ConfigSpace (Sym2 V) => (∀ e' ∈ γ, ω e' = false) ∧ ω e = true))
      = (Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ∀ e' ∈ γ, ω e' = false)).filter
          (fun ω => ¬ ω e = false) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_false]
  have hset0 : (Finset.univ.filter
        (fun ω : ConfigSpace (Sym2 V) => (∀ e' ∈ γ, ω e' = false) ∧ ω e = false))
      = (Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ∀ e' ∈ γ, ω e' = false)).filter
          (fun ω => ω e = false) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hset1, hset0, add_comm]
  exact (Finset.sum_filter_add_sum_filter_not
        (Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ∀ e' ∈ γ, ω e' = false))
        (fun ω => ω e = false) (fkProb G p q)).symm


theorem closedMass_insert_reindex {p q : ℝ} (e : Sym2 V) {γ : Finset (Sym2 V)} (he : e ∉ γ) :
    closedMass G p q (insert e γ)
      = ∑ ψ ∈ cfib e γ, fkProb G p q (setClosed e ψ) := by
  classical
  unfold closedMass cfib
  apply Finset.sum_nbij' (fun ω => ω) (fun ψ => ψ)
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.forall_mem_insert] at hω ⊢
    exact ⟨hω.1, hω.2⟩
  · intro ψ hψ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.forall_mem_insert] at hψ ⊢
    exact ⟨hψ.1, hψ.2⟩
  · intro ω _; rfl
  · intro ψ _; rfl
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.forall_mem_insert] at hω
    congr 1
    funext x; by_cases hx : x = e
    · subst hx; simp [hω.1]
    · rw [setClosed_of_ne hx]


theorem cFE_mul_closedMass_le_insert {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (e : Sym2 V) {γ : Finset (Sym2 V)} (he : e ∉ γ) :
    cFE p q * closedMass G p q γ ≤ closedMass G p q (insert e γ) := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  rw [closedMass_reindex G e he, closedMass_insert_reindex G e he, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ψ _
  
  have hZpos : 0 < fkZ G p q := fkZ_pos G hp hp1 hq0
  have hwt : cFE p q * (fkWeight G p q (setOpen e ψ) + fkWeight G p q (setClosed e ψ))
      ≤ fkWeight G p q (setClosed e ψ) := fkWeight_setClosed_ge G hp hp1 hq e ψ
  unfold fkProb
  rw [← add_div]
  rw [show cFE p q * ((fkWeight G p q (setOpen e ψ) + fkWeight G p q (setClosed e ψ)) / fkZ G p q)
      = (cFE p q * (fkWeight G p q (setOpen e ψ) + fkWeight G p q (setClosed e ψ))) / fkZ G p q
      from by ring]
  exact (div_le_div_iff_of_pos_right hZpos).mpr hwt


theorem cFE_pow_le_closedMass {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (γ : Finset (Sym2 V)) :
    cFE p q ^ γ.card ≤ closedMass G p q γ := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  classical
  induction γ using Finset.induction with
  | empty => rw [Finset.card_empty, pow_zero, closedMass_empty G hp hp1 hq0]
  | @insert e γ he ih =>
    rw [Finset.card_insert_of_notMem he, pow_succ]
    calc cFE p q ^ γ.card * cFE p q
        = cFE p q * cFE p q ^ γ.card := by ring
      _ ≤ cFE p q * closedMass G p q γ :=
          mul_le_mul_of_nonneg_left ih (cFE_pos hp hp1 hq).le
      _ ≤ closedMass G p q (insert e γ) := cFE_mul_closedMass_le_insert G hp hp1 hq e he


end FK
end StatMech
