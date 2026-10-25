/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.OptionalStopping.Part3
import Def.StatisticalMechanics.Code.OSSS.TailSelMP.Part2
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000


namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly

open StatMech.Probability OSSS.AdaptiveTau OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem tsm_tailSelMP_of_restrictedSum (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (hres : tsm_TailSelMP_restrictedSum μ σ f t s A) :
    atl_TailSelMP μ σ f t s A := by
  show MeasurePreserving (atl_selRand μ σ f t s A) ((ubfTail n t).prod (Vcube n)) (Vcube n)
  exact tsm_measurePreserving_of_partition
    (S := tsm_switchPiece μ σ f t A)
    (tsm_switchPiece_meas μ σ f t A) (tsm_switchPiece_disj μ σ f t A)
    (tsm_switchPiece_cover μ σ f t A)
    (h := atl_selRand μ σ f t s A)
    (tsm_measurable_selRand μ σ f t s A)
    (hk := fun k => osp_tailSelFixed t s k A)
    (fun k => osp_tailSelFixed_meas t s k A)
    (fun k p hp => tsm_selRand_eq_on_piece μ σ f t s A k p hp)
    hres


lemma tsm_switchPiece_const_eq (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) (k₀ : ℕ)
    (hconst : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) = k₀) :
    tsm_switchPiece μ σ f t A k₀ = Set.univ := by
  ext p
  simp only [tsm_switchPiece, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact hconst p.1


lemma tsm_switchPiece_const_empty (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) (k₀ : ℕ)
    (hconst : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ, stopVal μ σ f (acp_join t A B) = k₀)
    (k : ℕ) (hk : k ≠ k₀) :
    tsm_switchPiece μ σ f t A k = ∅ := by
  ext p
  simp only [tsm_switchPiece, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hpk
  exact hk (by rw [← hpk, hconst p.1])


theorem tsm_restrictedSum_of_const (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (t s : ℕ) (hts : t ≤ s) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (k₀ : ℕ) (hconst : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ,
        stopVal μ σ f (acp_join t A B) = k₀) :
    tsm_TailSelMP_restrictedSum μ σ f t s A := by
  show (Measure.sum (fun k => Measure.map (osp_tailSelFixed t s k A)
      (((ubfTail n t).prod (Vcube n)).restrict (tsm_switchPiece μ σ f t A k)))) = Vcube n
  
  have hzero : ∀ k, k ≠ k₀ → Measure.map (osp_tailSelFixed t s k A)
      (((ubfTail n t).prod (Vcube n)).restrict (tsm_switchPiece μ σ f t A k)) = 0 := by
    intro k hk
    rw [tsm_switchPiece_const_empty μ σ t A k₀ hconst k hk, Measure.restrict_empty,
      Measure.map_zero]
  
  rw [show (Measure.sum (fun k => Measure.map (osp_tailSelFixed t s k A)
        (((ubfTail n t).prod (Vcube n)).restrict (tsm_switchPiece μ σ f t A k))))
      = Measure.map (osp_tailSelFixed t s k₀ A)
        (((ubfTail n t).prod (Vcube n)).restrict (tsm_switchPiece μ σ f t A k₀)) from by
    ext T hT
    rw [Measure.sum_apply _ hT]
    exact tsum_eq_single k₀ (fun k hk => by rw [hzero k hk]; rfl)]
  
  rw [tsm_switchPiece_const_eq μ σ t A k₀ hconst, Measure.restrict_univ]
  exact (osp_tailSelFixed_mp t s k₀ hts A).map_eq


theorem tsm_tailSelMP_of_const_switch (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (t s : ℕ) (hts : t ≤ s) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (k₀ : ℕ) (hconst : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ,
        stopVal μ σ f (acp_join t A B) = k₀) :
    atl_TailSelMP μ σ f t s A :=
  tsm_tailSelMP_of_restrictedSum μ σ f t s A
    (tsm_restrictedSum_of_const μ σ t s hts A k₀ hconst)

end AdaptDisintegration
end OSSS
end StatMech
