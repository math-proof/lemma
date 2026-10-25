/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKMixingClose
import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part6
import Def.StatisticalMechanics.Code.FK.FKMixingUpperClose.Part2
open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open ConfigSpace

variable {E : Type*} {G : Type*} [Group G] [MulAction G E]


variable {μ : Measure (ConfigSpace E)} [IsProbabilityMeasure μ]

theorem fmu_traceInd_eq_prod (F : Finset E) (τ : E → Bool) (ω : ConfigSpace E) :
    fmu_traceInd F τ ω = ∏ e ∈ F, (if τ e then fmu_xR ω e else (1 - fmu_xR ω e)) := by
  unfold fmu_traceInd fmu_xR; classical
  by_cases h : ∀ e ∈ F, ω e = τ e
  · rw [if_pos h]; symm; apply Finset.prod_eq_one; intro e he
    have : ω e = τ e := h e he
    rcases hτ : τ e with _ | _ <;> rw [hτ] at this <;> simp_all
  · rw [if_neg h]; symm
    rw [not_forall] at h; obtain ⟨e, he⟩ := h; rw [Classical.not_imp] at he
    obtain ⟨heF, hev⟩ := he
    apply Finset.prod_eq_zero heF
    rcases hτ : τ e with _ | _ <;> rcases hω : ω e with _ | _ <;> simp_all


theorem fmu_traceInd_expand [DecidableEq E] (F : Finset E) (τ : E → Bool) (ω : ConfigSpace E) :
    fmu_traceInd F τ ω = ∑ T ∈ F.powerset, fmu_traceCoef F τ T * fmu_moInd T ω := by
  rw [fmu_traceInd_eq_prod]
  have hfac : ∀ e, (if τ e then fmu_xR ω e else (1 - fmu_xR ω e))
      = (if τ e then (1:ℝ) else -1) * fmu_xR ω e + (if τ e then (0:ℝ) else 1) := by
    intro e; rcases τ e with _ | _
    · simp only [Bool.false_eq_true, if_false]; ring
    · simp only [if_true]; ring
  simp_rw [hfac]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl; intro T hT
  unfold fmu_traceCoef fmu_moInd; rw [Finset.prod_mul_distrib]; ring


theorem fmu_cylinder_indicator_eq_sum_traceInd [DecidableEq E] (F : Finset E)
    (Sf : Finset (↥F → Bool)) (ω : ConfigSpace E) :
    (cylinder F (↑Sf : Set (↥F → Bool))).indicator (fun _ => (1:ℝ)) ω
      = ∑ σ ∈ Sf, fmu_traceInd F (fun e => if h : e ∈ F then σ ⟨e, h⟩ else false) ω := by
  classical
  by_cases hmem : ω ∈ cylinder F (↑Sf : Set (↥F → Bool))
  · rw [Set.indicator_of_mem hmem]
    rw [mem_cylinder] at hmem
    rw [Finset.sum_eq_single (F.restrict ω)]
    · unfold fmu_traceInd; rw [if_pos]
      intro e he; simp only []; rw [dif_pos he, Finset.restrict_def]
    · intro σ hσ hne
      unfold fmu_traceInd; rw [if_neg]
      intro hcontra
      apply hne; funext e
      have := hcontra e.1 e.2
      simp only [Finset.restrict_def] at this ⊢
      rw [this]; simp [e.2]
    · intro h; exact absurd (Finset.mem_coe.mp hmem) h
  · rw [Set.indicator_of_notMem hmem]
    rw [mem_cylinder] at hmem
    symm; apply Finset.sum_eq_zero; intro σ hσ
    unfold fmu_traceInd; rw [if_neg]
    intro hcontra; apply hmem
    have : F.restrict ω = σ := by
      funext e; have := hcontra e.1 e.2; simp only [Finset.restrict_def] at this ⊢
      rw [this]; simp [e.2]
    rw [Finset.mem_coe, this]; exact hσ


theorem fmu_cylinder_expand [DecidableEq E] (A : Set (ConfigSpace E))
    (hA : A ∈ measurableCylinders (fun _ : E => Bool)) :
    ∃ (P : Finset (Finset E)) (c : Finset E → ℝ),
      ∀ ω, A.indicator (fun _ => (1:ℝ)) ω = ∑ T ∈ P, c T * fmu_moInd T ω := by
  classical
  rw [mem_measurableCylinders] at hA
  obtain ⟨F, S, hSmeas, rfl⟩ := hA
  set Sf : Finset (↥F → Bool) := S.toFinset with hSf
  have hScoe : S = (↑Sf : Set (↥F → Bool)) := by rw [hSf, Set.coe_toFinset]
  refine ⟨F.powerset, fun T => ∑ σ ∈ Sf,
      fmu_traceCoef F (fun e => if h : e ∈ F then σ ⟨e, h⟩ else false) T, ?_⟩
  intro ω
  rw [hScoe, fmu_cylinder_indicator_eq_sum_traceInd F Sf ω]
  simp_rw [fmu_traceInd_expand F]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro T hT
  rw [Finset.sum_mul]


theorem fmu_real_eq_sum [Countable E] {C : Set (ConfigSpace E)} (hC : MeasurableSet C)
    (P : Finset (Finset E)) (c : Finset E → ℝ)
    (hexp : ∀ ω, C.indicator (fun _ => (1:ℝ)) ω = ∑ T ∈ P, c T * fmu_moInd T ω) :
    μ.real C = ∑ T ∈ P, c T * μ.real (fmu_multiOpen T) := by
  have h1 : μ.real C = ∫ ω, C.indicator (fun _ => (1:ℝ)) ω ∂μ := by
    rw [MeasureTheory.integral_indicator_const (1:ℝ) hC]; simp
  rw [h1]
  simp_rw [hexp]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl; intro T hT
    rw [MeasureTheory.integral_const_mul, fmu_integral_moInd]
  · intro T hT
    exact (fmu_integrable_moInd T).const_mul _


theorem fmu_real_inter_shift_eq_sum [Countable E] (g : G) {C : Set (ConfigSpace E)}
    (hC : MeasurableSet C)
    (P : Finset (Finset E)) (c : Finset E → ℝ)
    (hexp : ∀ ω, C.indicator (fun _ => (1:ℝ)) ω = ∑ T ∈ P, c T * fmu_moInd T ω) :
    μ.real (C ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' C)
      = ∑ T ∈ P, ∑ T' ∈ P, c T * c T' *
          μ.real (fmu_multiOpen T ∩
            (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T') := by
  classical
  have hmeas2 : MeasurableSet (C ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' C) :=
    hC.inter (hC.preimage (measurable_shift g))
  have hkey : μ.real (C ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' C)
      = ∫ ω, (C.indicator (fun _ => (1:ℝ)) ω) * (C.indicator (fun _ => (1:ℝ)) (shift g ω)) ∂μ := by
    rw [show μ.real (C ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' C)
          = ∫ ω, (C ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' C).indicator
            (fun _ => (1:ℝ)) ω ∂μ from by
      rw [MeasureTheory.integral_indicator_const (1:ℝ) hmeas2]; simp]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with ω
    have hcomp : C.indicator (fun _ => (1:ℝ)) (shift g ω)
        = ((shift g : ConfigSpace E → ConfigSpace E) ⁻¹' C).indicator (fun _ => (1:ℝ)) ω :=
      (Set.indicator_comp_right (s := C)
        (f := (shift g : ConfigSpace E → ConfigSpace E)) (g := fun _ => (1:ℝ)) (x := ω)).symm
    rw [hcomp, fmu_indicator_mul_indicator]
  rw [hkey]
  simp_rw [hexp]
  have hpoint : ∀ ω, (∑ T ∈ P, c T * fmu_moInd T ω) *
      (∑ T' ∈ P, c T' * fmu_moInd T' (shift g ω))
      = ∑ T ∈ P, ∑ T' ∈ P, (c T * c T') * (fmu_moInd T ω * fmu_moInd T' (shift g ω)) := by
    intro ω
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro T hT
    apply Finset.sum_congr rfl; intro T' hT'; ring
  simp_rw [hpoint]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl; intro T hT
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl; intro T' hT'
      rw [MeasureTheory.integral_const_mul]
      congr 1
      rw [fmu_moInd_mul_shift_eq g T T']
      rw [MeasureTheory.integral_indicator_const (1:ℝ)
        ((fmu_multiOpen_measurable T).inter
          ((fmu_multiOpen_measurable T').preimage (measurable_shift g)))]
      simp
    · intro T' hT'
      exact (fmu_integrable_moInd_mul_shift g T T').const_mul _
  · intro T hT
    apply MeasureTheory.integrable_finsetSum
    intro T' hT'
    exact (fmu_integrable_moInd_mul_shift g T T').const_mul _


end FK
end StatMech
