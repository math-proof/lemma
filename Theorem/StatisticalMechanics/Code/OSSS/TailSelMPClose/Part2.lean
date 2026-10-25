/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TailSelMPClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.TailSelMP.Part3
import Def.StatisticalMechanics.Code.OSSS.TailSelMPClose
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


lemma tsc_recover_meas (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    Measurable (tsc_recover μ σ f t A) := by
  have hjoin : Measurable (fun W : Fin n → ℝ => acp_join t A ((ubfSplit n t W).2)) := by
    show Measurable (fun W : Fin n → ℝ => (ubfSplit n t).symm (A, (ubfSplit n t W).2))
    exact (ubfSplit n t).symm.measurable.comp (measurable_const.prodMk
      (measurable_snd.comp (ubfSplit n t).measurable))
  exact (measurable_stopVal μ σ f).comp hjoin


theorem tsc_recover_eq_of_piece (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t k : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ))
    (hp : stopVal μ σ f (acp_join t A p.1) = k) :
    tsc_recover μ σ f t A (osp_tailSelFixed t t k A p) = k := by
  obtain ⟨B, V⟩ := p
  
  have hagree_in : ∀ i : Fin n, (i : ℕ) < k →
      acp_join t A ((ubfSplit n t (osp_tailSelFixed t t k A (B, V))).2) i = acp_join t A B i := by
    intro i hik
    by_cases hi : (i : ℕ) < t
    · rw [tsc_acp_join_head t A _ i hi, tsc_acp_join_head t A B i hi]
    · rw [tsc_acp_join_tail t A _ i hi, tsc_acp_join_tail t A B i hi, ubfSplit_apply_snd]
      show adaptWt (acp_join t A B) V k t i = B ⟨i, hi⟩
      unfold adaptWt
      simp only [hi, if_false, hik, if_true]
      exact tsc_acp_join_tail t A B i hi
  
  have hcode : ∀ e ∈ prefixSet (σ : Fin n → E) k,
      codeMap μ (σ : Fin n → E) (acp_join t A B) e
        = codeMap μ (σ : Fin n → E)
            (acp_join t A ((ubfSplit n t (osp_tailSelFixed t t k A (B, V))).2)) e :=
    fun e he => (codeMap_agree_on_prefix μ σ _ (acp_join t A B) k hagree_in e he).symm
  show stopValC σ f
      (codeMap μ (σ : Fin n → E)
        (acp_join t A ((ubfSplit n t (osp_tailSelFixed t t k A (B, V))).2))) = k
  exact tsc_stopValC_stable σ f (codeMap μ (σ : Fin n → E) (acp_join t A B)) _ k hcode
    (by rw [← stopVal_eq_stopValC]; exact hp)


lemma tsc_piece_subset_recover (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) (k : ℕ) :
    tsm_switchPiece μ σ f t A k
      ⊆ (osp_tailSelFixed t t k A) ⁻¹' ((tsc_recover μ σ f t A) ⁻¹' {k}) := by
  intro p hp
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact tsc_recover_eq_of_piece μ σ f t k A p hp


theorem tsc_restrictedSum_at_s_eq_t (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    tsm_TailSelMP_restrictedSum μ σ f t t A := by
  show (Measure.sum (fun k => Measure.map (osp_tailSelFixed t t k A)
      (((ubfTail n t).prod (Vcube n)).restrict (tsm_switchPiece μ σ f t A k)))) = Vcube n
  exact tsc_restrictedSum_of_recover
    (S := tsm_switchPiece μ σ f t A)
    (Φ := fun k => osp_tailSelFixed t t k A)
    (R := tsc_recover μ σ f t A)
    (tsm_switchPiece_meas μ σ f t A) (tsm_switchPiece_disj μ σ f t A)
    (tsm_switchPiece_cover μ σ f t A)
    (fun k => osp_tailSelFixed_meas t t k A) (tsc_recover_meas μ σ f t A)
    (fun k => osp_tailSelFixed_mp t t k (le_refl t) A)
    (tsc_piece_subset_recover μ σ f t A)


theorem tsc_tailSelMP_at_s_eq_t (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    atl_TailSelMP μ σ f t t A :=
  tsm_tailSelMP_of_restrictedSum μ σ f t t A (tsc_restrictedSum_at_s_eq_t μ σ f t A)

end AdaptDisintegration
end OSSS
end StatMech
