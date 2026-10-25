/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/StepCov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.LindebergTree.Part6
import Def.StatisticalMechanics.Code.OSSS.StepCov
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace StepCov

open OSSS.Monotonic OSSS.Coding OSSS.Lindeberg OSSS.LindebergTree

open OSSS.DecisionTree

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma abs_step_freshAt_eq_sum_prefix {μ : ConfigSpace E → ℝ} (T : DecisionTree E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (e : E) (ω : ConfigSpace E) :
    |adaptM μ T f (t + 1) ω - adaptM μ T f t ω| * freshAt T ω t e
      = ∑ F ∈ prefSet e,
          |cExp μ (insert e F) f ω - cExp μ F f ω| * freshPI T ω t e F := by
  set P := pathPrefix T ω t with hP
  by_cases hPe : e ∈ P
  · 
    have hfresh0 : freshAt T ω t e = 0 := by
      unfold freshAt; rw [if_neg (by rintro ⟨_, h2⟩; rw [← hP] at h2; exact h2 hPe)]
    rw [hfresh0, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro F hF
    rw [prefSet, Finset.mem_filter] at hF
    
    unfold freshPI
    rw [if_neg (by rintro ⟨h1, _⟩; rw [hP, h1] at hPe; exact hF.2 hPe)]
    simp
  · 
    have hPmem : P ∈ prefSet e := by rw [prefSet, Finset.mem_filter]; exact ⟨Finset.mem_univ P, hPe⟩
    rw [Finset.sum_eq_single_of_mem P hPmem]
    · unfold freshAt freshPI adaptM
      rw [← hP]
      by_cases hgrow : pathPrefix T ω (t + 1) = insert e P
      · have he_in : e ∈ pathPrefix T ω (t + 1) := by rw [hgrow]; exact Finset.mem_insert_self e P
        rw [if_pos ⟨he_in, hPe⟩, if_pos ⟨rfl, hgrow⟩, hgrow]
      · have hfresh0 : ¬ (e ∈ pathPrefix T ω (t + 1) ∧ e ∉ P) := by
          rintro ⟨hin, hnin⟩
          rcases pathPrefix_succ_eq_or_insert T ω t with heq | ⟨a, hanew, ha⟩
          · rw [← hP] at heq; rw [heq] at hin; exact hnin hin
          · rw [← hP] at ha hanew
            rw [ha] at hin
            rcases Finset.mem_insert.mp hin with rfl | hmem
            · exact hgrow (by rw [ha])
            · exact hnin hmem
        rw [if_neg hfresh0, if_neg (by rintro ⟨_, h2⟩; exact hgrow h2)]
        simp
    · 
      intro F _ hFne
      unfold freshPI
      rw [if_neg (by rintro ⟨h1, _⟩; exact hFne (by rw [← h1, ← hP]))]
      simp


lemma freshPI_Fmeas (T : DecisionTree E) (t : ℕ) (e : E) (F : Finset E) :
    Fmeas F (fun ω => freshPI T ω t e F) := freshPref_Fmeas T F e t


lemma freshPI_nonneg (T : DecisionTree E) (ω : ConfigSpace E) (t : ℕ) (e : E) (F : Finset E) :
    0 ≤ freshPI T ω t e F := by unfold freshPI; split <;> norm_num


lemma mean_step_eq_sum_prefix {μ : ConfigSpace E → ℝ} (T : DecisionTree E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (e : E) :
    mean μ (fun ω => |adaptM μ T f (t + 1) ω - adaptM μ T f t ω| * freshAt T ω t e)
      = ∑ F ∈ prefSet e,
          mean μ (fun ω =>
            |cExp μ (insert e F) f ω - cExp μ F f ω| * freshPI T ω t e F) := by
  unfold mean
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp only []
  rw [abs_step_freshAt_eq_sum_prefix T f t e ω, Finset.sum_mul]


theorem mean_step_freshAt_eq {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hFKG : FKGLatticeCondition μ) (T : DecisionTree E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (t : ℕ) (e : E) :
    mean μ (fun ω => |adaptM μ T f (t + 1) ω - adaptM μ T f t ω| * freshAt T ω t e)
      = 2 * ∑ F ∈ prefSet e,
          mean μ (fun ω => (freshPI T ω t e F * delta μ F e f ω)
            * (cExp μ F (coord e) ω * (1 - cExp μ F (coord e) ω))) := by
  rw [mean_step_eq_sum_prefix T f t e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro F hF
  rw [prefSet, Finset.mem_filter] at hF
  have hcomm : mean μ (fun ω => |cExp μ (insert e F) f ω - cExp μ F f ω| * freshPI T ω t e F)
      = mean μ (fun ω => freshPI T ω t e F * |cExp μ (insert e F) f ω - cExp μ F f ω|) := by
    unfold mean; exact Finset.sum_congr rfl (fun ω _ => by ring)
  rw [hcomm]
  exact stepAbs_eq_two_mul hpos hFKG F e hF.2 hf hf0 (freshPI_Fmeas T t e F)


lemma freshAt_eq_sum_prefix (T : DecisionTree E) (ω : ConfigSpace E) (t : ℕ) (e : E) :
    freshAt T ω t e = ∑ F ∈ prefSet e, freshPI T ω t e F := by
  
  
  set P := pathPrefix T ω t with hP
  by_cases hPe : e ∈ P
  · have hfresh0 : freshAt T ω t e = 0 := by
      unfold freshAt; rw [if_neg (by rintro ⟨_, h2⟩; rw [← hP] at h2; exact h2 hPe)]
    rw [hfresh0]
    symm
    apply Finset.sum_eq_zero
    intro F hF
    rw [prefSet, Finset.mem_filter] at hF
    unfold freshPI
    rw [if_neg (by rintro ⟨h1, _⟩; rw [hP, h1] at hPe; exact hF.2 hPe)]
  · have hPmem : P ∈ prefSet e := by rw [prefSet, Finset.mem_filter]; exact ⟨Finset.mem_univ P, hPe⟩
    rw [Finset.sum_eq_single_of_mem P hPmem]
    · unfold freshAt freshPI
      rw [← hP]
      by_cases hgrow : pathPrefix T ω (t + 1) = insert e P
      · have he_in : e ∈ pathPrefix T ω (t + 1) := by rw [hgrow]; exact Finset.mem_insert_self e P
        rw [if_pos ⟨he_in, hPe⟩, if_pos ⟨rfl, hgrow⟩]
      · have hfresh0 : ¬ (e ∈ pathPrefix T ω (t + 1) ∧ e ∉ P) := by
          rintro ⟨hin, hnin⟩
          rcases pathPrefix_succ_eq_or_insert T ω t with heq | ⟨a, hanew, ha⟩
          · rw [← hP] at heq; rw [heq] at hin; exact hnin hin
          · rw [← hP] at ha hanew
            rw [ha] at hin
            rcases Finset.mem_insert.mp hin with rfl | hmem
            · exact hgrow (by rw [ha])
            · exact hnin hmem
        rw [if_neg hfresh0, if_neg (by rintro ⟨_, h2⟩; exact hgrow h2)]
    · intro F _ hFne
      unfold freshPI
      rw [if_neg (by rintro ⟨h1, _⟩; exact hFne (by rw [← h1, ← hP]))]


lemma mean_freshAt_eq_sum_prefix {μ : ConfigSpace E → ℝ} (T : DecisionTree E) (t : ℕ) (e : E) :
    mean μ (fun ω => freshAt T ω t e) = ∑ F ∈ prefSet e, mean μ (fun ω => freshPI T ω t e F) := by
  unfold mean
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp only []
  rw [freshAt_eq_sum_prefix T ω t e, Finset.sum_mul]


end StepCov
end OSSS
end StatMech
