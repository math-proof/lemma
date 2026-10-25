/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxDomainMarkov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

variable (C : SimpleGraph V) [DecidableRel C.Adj]


theorem indicator_const_on_fibre {F : Finset (Sym2 V)} {B : Set (ConfigSpace (Sym2 V))}
    (hB : DependsOnOutside F B) {ψ ρ : ConfigSpace (Sym2 V)} (hρ : AgreesOff F ψ ρ) :
    B.indicator (fun _ => (1:ℝ)) ρ = B.indicator (fun _ => (1:ℝ)) ψ := by
  by_cases h : ψ ∈ B
  · rw [Set.indicator_of_mem ((hB ψ ρ hρ).mp h), Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (fun hh => h ((hB ψ ρ hρ).mpr hh)),
      Set.indicator_of_notMem h]


theorem condBcProb_sum_outside {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    {F : Finset (Sym2 V)} {B : Set (ConfigSpace (Sym2 V))} (hB : DependsOnOutside F B)
    {ψ : ConfigSpace (Sym2 V)} (hψ : projOff F ψ = ψ) :
    (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ)
      = B.indicator (fun _ => (1:ℝ)) ψ := by
  classical
  have hrestrict : (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ)
      = ∑ ρ ∈ condFibre F ψ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro ρ _ hρ
    rw [mem_condFibre] at hρ
    unfold condBcProb; rw [if_neg hρ, mul_zero]
  rw [hrestrict]
  have hconst : ∀ ρ ∈ condFibre F ψ,
      B.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ
        = B.indicator (fun _ => (1:ℝ)) ψ * condBcProb G C p q F ψ ρ := by
    intro ρ hρ
    rw [mem_condFibre] at hρ
    rw [indicator_const_on_fibre hB hρ]
  rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum]
  have hsum1 : ∑ ρ ∈ condFibre F ψ, condBcProb G C p q F ψ ρ = 1 := by
    have htot : ∑ ρ, condBcProb G C p q F ψ ρ = 1 := condBcProb_sum_eq_one G C hp hp1 hq F ψ
    rw [← htot]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro ρ _ hρ
    rw [mem_condFibre] at hρ
    unfold condBcProb; rw [if_neg hρ]
  rw [hsum1, mul_one]


theorem condBcProb_cross_outside {p q : ℝ}
    {F : Finset (Sym2 V)} {A B : Set (ConfigSpace (Sym2 V))} (hB : DependsOnOutside F B)
    {ψ : ConfigSpace (Sym2 V)} :
    (∑ ρ, (A ∩ B).indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ)
      = B.indicator (fun _ => (1:ℝ)) ψ *
          (∑ ρ, A.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ _
  by_cases hρ : AgreesOff F ψ ρ
  · have hBρ : B.indicator (fun _ => (1:ℝ)) ρ = B.indicator (fun _ => (1:ℝ)) ψ :=
      indicator_const_on_fibre hB hρ
    have hAB : (A ∩ B).indicator (fun _ => (1:ℝ)) ρ
        = A.indicator (fun _ => (1:ℝ)) ρ * B.indicator (fun _ => (1:ℝ)) ρ := by
      by_cases ha : ρ ∈ A <;> by_cases hb : ρ ∈ B <;>
        simp [Set.indicator, ha, hb, Set.mem_inter_iff]
    rw [hAB, hBρ]; ring
  · unfold condBcProb; rw [if_neg hρ]; ring


theorem bcProb_disjoint_product_dom {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    {F : Finset (Sym2 V)} {A B : Set (ConfigSpace (Sym2 V))} (hB : DependsOnOutside F B)
    {α : ℝ} (hα : 0 ≤ α)
    (hres : ∀ ψ ∈ fibreReps F,
      (∑ ρ, A.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ) ≤ α) :
    (∑ ρ, (A ∩ B).indicator (fun _ => (1:ℝ)) ρ * bcProb G C p q ρ)
      ≤ α * (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * bcProb G C p q ρ) := by
  classical
  rw [bcProb_fibre_decompose G C hp hp1 hq F (A ∩ B),
      bcProb_fibre_decompose G C hp hp1 hq F B, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ψ hψ
  rw [fibreReps, Finset.mem_filter] at hψ
  have hfm : 0 ≤ ∑ σ ∈ condFibre F ψ, bcProb G C p q σ :=
    Finset.sum_nonneg (fun σ _ => bcProb_nonneg G C hp hp1 hq σ)
  have hBcond : (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ)
      = B.indicator (fun _ => (1:ℝ)) ψ :=
    condBcProb_sum_outside G C hp hp1 hq hB hψ.2
  have hABcond : (∑ ρ, (A ∩ B).indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ)
      = B.indicator (fun _ => (1:ℝ)) ψ *
          (∑ ρ, A.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ) :=
    condBcProb_cross_outside G C hB
  rw [hABcond, hBcond]
  have hBind : 0 ≤ B.indicator (fun _ => (1:ℝ)) ψ := Set.indicator_nonneg (fun _ _ => zero_le_one) ψ
  have hres' := hres ψ (Finset.mem_filter.mpr hψ)
  calc (∑ σ ∈ condFibre F ψ, bcProb G C p q σ)
          * (B.indicator (fun _ => (1:ℝ)) ψ *
              (∑ ρ, A.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ))
      ≤ (∑ σ ∈ condFibre F ψ, bcProb G C p q σ) * (B.indicator (fun _ => (1:ℝ)) ψ * α) := by
        apply mul_le_mul_of_nonneg_left _ hfm
        exact mul_le_mul_of_nonneg_left hres' hBind
    _ = α * ((∑ σ ∈ condFibre F ψ, bcProb G C p q σ) * B.indicator (fun _ => (1:ℝ)) ψ) := by ring


theorem bcProb_disjoint_product_lower_of_conditional
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    {F : Finset (Sym2 V)} {A B : Set (ConfigSpace (Sym2 V))}
    (hB : DependsOnOutside F B) {α : ℝ}
    (hres : ∀ ψ ∈ fibreReps F, α ≤
      ∑ ρ, A.indicator (fun _ => (1 : ℝ)) ρ *
        condBcProb G C p q F ψ ρ) :
    α * (∑ ρ, B.indicator (fun _ => (1 : ℝ)) ρ *
          bcProb G C p q ρ) ≤
      ∑ ρ, (A ∩ B).indicator (fun _ => (1 : ℝ)) ρ *
        bcProb G C p q ρ := by
  classical
  rw [bcProb_fibre_decompose G C hp hp1 hq F (A ∩ B),
    bcProb_fibre_decompose G C hp hp1 hq F B, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ψ hψ
  rw [fibreReps, Finset.mem_filter] at hψ
  have hfm : 0 ≤ ∑ σ ∈ condFibre F ψ, bcProb G C p q σ :=
    Finset.sum_nonneg (fun σ _ => bcProb_nonneg G C hp hp1 hq σ)
  have hBcond :
      (∑ ρ, B.indicator (fun _ => (1 : ℝ)) ρ *
          condBcProb G C p q F ψ ρ) =
        B.indicator (fun _ => (1 : ℝ)) ψ :=
    condBcProb_sum_outside G C hp hp1 hq hB hψ.2
  have hABcond :
      (∑ ρ, (A ∩ B).indicator (fun _ => (1 : ℝ)) ρ *
          condBcProb G C p q F ψ ρ) =
        B.indicator (fun _ => (1 : ℝ)) ψ *
          (∑ ρ, A.indicator (fun _ => (1 : ℝ)) ρ *
            condBcProb G C p q F ψ ρ) :=
    condBcProb_cross_outside G C hB
  rw [hBcond, hABcond]
  have hBind : 0 ≤ B.indicator (fun _ => (1 : ℝ)) ψ :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) ψ
  have hres' := hres ψ (Finset.mem_filter.mpr hψ)
  calc
    α * ((∑ σ ∈ condFibre F ψ, bcProb G C p q σ) *
        B.indicator (fun _ => (1 : ℝ)) ψ) =
      (∑ σ ∈ condFibre F ψ, bcProb G C p q σ) *
        (B.indicator (fun _ => (1 : ℝ)) ψ * α) := by ring
    _ ≤ (∑ σ ∈ condFibre F ψ, bcProb G C p q σ) *
        (B.indicator (fun _ => (1 : ℝ)) ψ *
          (∑ ρ, A.indicator (fun _ => (1 : ℝ)) ρ *
            condBcProb G C p q F ψ ρ)) := by
      apply mul_le_mul_of_nonneg_left _ hfm
      exact mul_le_mul_of_nonneg_left hres' hBind


theorem perFibre_dom_of_wired {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {F : Finset (Sym2 V)} (C' : SimpleGraph V) [DecidableRel C'.Adj] (hCC' : C ≤ C')
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) {α : ℝ}
    (hres' : ∀ ψ ∈ fibreReps F,
      (∑ ρ, A.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C' p q F ψ ρ) ≤ α) :
    ∀ ψ ∈ fibreReps F,
      (∑ ρ, A.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C p q F ψ ρ) ≤ α := by
  intro ψ hψ
  exact le_trans (condBcProb_mono_bc G C C' hCC' hp hp1 hq F ψ hA) (hres' ψ hψ)


theorem bcProb_disjoint_product_dom_wired {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {F : Finset (Sym2 V)} (C' : SimpleGraph V) [DecidableRel C'.Adj] (hCC' : C ≤ C')
    {A B : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) (hB : DependsOnOutside F B)
    {α : ℝ} (hα : 0 ≤ α)
    (hres' : ∀ ψ ∈ fibreReps F,
      (∑ ρ, A.indicator (fun _ => (1:ℝ)) ρ * condBcProb G C' p q F ψ ρ) ≤ α) :
    (∑ ρ, (A ∩ B).indicator (fun _ => (1:ℝ)) ρ * bcProb G C p q ρ)
      ≤ α * (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * bcProb G C p q ρ) :=
  bcProb_disjoint_product_dom G C hp hp1 (lt_of_lt_of_le one_pos hq) hB hα
    (perFibre_dom_of_wired G C hp hp1 hq C' hCC' hA hres')

end FK
end StatMech
