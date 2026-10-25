/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABFieldDeriv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.Russo
import Theorem.StatisticalMechanics.Code.Sharpness.AizenmanBarskyUncond
import Theorem.StatisticalMechanics.Code.Sharpness.BetaReparam
import Def.StatisticalMechanics.Code.Sharpness.ABFieldDeriv.Part2
open MeasureTheory Set Finset Function
open scoped NNReal ENNReal

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Sharpness

open ConfigSpace StatMech


variable {E : Type*} [Fintype E] [DecidableEq E]


lemma configWeightV_paramOn_factor (s : Finset E) (p : E → ℝ) (ω : ConfigSpace E) (c : ℝ) :
    configWeightV (paramOn s c p) ω
      = (∏ e ∈ s, (if ω e then c else 1 - c))
        * ∏ e ∈ univ \ s, (if ω e then p e else 1 - p e) := by
  unfold configWeightV edgeWeightV paramOn
  rw [← Finset.prod_filter_mul_prod_filter_not univ (· ∈ s)]
  congr 1
  · rw [show univ.filter (· ∈ s) = s by
          ext j; simp]
    apply Finset.prod_congr rfl
    intro e he; rw [if_pos he]
  · rw [show univ.filter (fun j => ¬ j ∈ s) = (univ \ s : Finset E) by
          ext j; simp]
    apply Finset.prod_congr rfl
    intro e he
    have : e ∉ s := (Finset.mem_sdiff.mp he).2
    rw [if_neg this]


lemma weightOffV_paramOn_mem (s : Finset E) (p : E → ℝ) (ω : ConfigSpace E) (c : ℝ)
    {e : E} (he : e ∈ s) :
    weightOffV (paramOn s c p) e ω
      = (∏ j ∈ s.erase e, (if ω j then c else 1 - c))
        * ∏ j ∈ univ \ s, (if ω j then p j else 1 - p j) := by
  unfold weightOffV edgeWeightV paramOn
  
  rw [← Finset.prod_filter_mul_prod_filter_not (univ.erase e) (· ∈ s)]
  congr 1
  · 
    rw [show (univ.erase e).filter (· ∈ s) = s.erase e by
          ext j
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ]
          tauto]
    apply Finset.prod_congr rfl
    intro j hj
    rw [if_pos (Finset.mem_of_mem_erase hj)]
  · 
    rw [show (univ.erase e).filter (fun j => ¬ j ∈ s) = (univ \ s : Finset E) by
          ext j
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
            Finset.mem_sdiff]
          constructor
          · rintro ⟨_, hj⟩; exact ⟨trivial, hj⟩
          · rintro ⟨_, hj⟩
            refine ⟨⟨?_, trivial⟩, hj⟩
            rintro rfl; exact hj he]
    apply Finset.prod_congr rfl
    intro j hj
    have : j ∉ s := (Finset.mem_sdiff.mp hj).2
    rw [if_neg this]


theorem hasDerivAt_probV_paramOn (s : Finset E) (p : E → ℝ) (A : Set (ConfigSpace E))
    (hA : IsIncreasing A) (c : ℝ) :
    HasDerivAt (fun c => probV (paramOn s c p) A)
      (∑ e ∈ s, pivotalProbV (paramOn s c p) A e) c := by
  
  
  set off : ConfigSpace E → ℝ :=
    fun ω => ∏ e ∈ univ \ s, (if ω e then p e else 1 - p e) with hoff
  have hfun : (fun c => probV (paramOn s c p) A)
      = fun c => ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
          * ((∏ e ∈ s, (if ω e then c else 1 - c)) * off ω) := by
    funext c
    unfold probV
    apply Finset.sum_congr rfl
    intro ω _
    rw [configWeightV_paramOn_factor s p ω c]
  rw [hfun]
  
  
  have hderiv : HasDerivAt
      (fun c => ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
          * ((∏ e ∈ s, (if ω e then c else 1 - c)) * off ω))
      (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
          * ((∑ e ∈ s, (if ω e then (1 : ℝ) else -1)
              * ∏ j ∈ s.erase e, (if ω j then c else 1 - c)) * off ω)) c := by
    apply HasDerivAt.fun_sum
    intro ω _
    
    have hprod : HasDerivAt (fun c => ∏ e ∈ s, (if ω e then c else 1 - c))
        (∑ e ∈ s, (if ω e then (1 : ℝ) else -1)
            * ∏ j ∈ s.erase e, (if ω j then c else 1 - c)) c := by
      have h := HasDerivAt.finsetProd (u := s)
        (f := fun e c => if ω e then c else 1 - c)
        (f' := fun e => if ω e then (1 : ℝ) else -1)
        (fun e _ => hasDerivAt_singleEdgeFactor ω e c)
      simp only [smul_eq_mul] at h
      convert h using 1
      · funext q; simp [Finset.prod_apply]
      · apply Finset.sum_congr rfl
        intro e he
        by_cases hωe : ω e = true <;> simp [hωe]
    exact ((hprod.mul_const (off ω)).const_mul (A.indicator (fun _ => (1 : ℝ)) ω))
  
  convert hderiv using 1
  
  
  have hrewrite : (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω
        * ((∑ e ∈ s, (if ω e then (1 : ℝ) else -1)
            * ∏ j ∈ s.erase e, (if ω j then c else 1 - c)) * off ω))
      = ∑ ω, ∑ e ∈ s, A.indicator (fun _ => (1 : ℝ)) ω
          * ((if ω e then (1 : ℝ) else -1) * weightOffV (paramOn s c p) e ω) := by
    apply Finset.sum_congr rfl
    intro ω _
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [weightOffV_paramOn_mem s p ω c he, hoff]
    ring
  rw [hrewrite, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  exact (abfd_russo_per_edge (paramOn s c p) A hA e).symm


omit [DecidableEq E] in


lemma configWeightV_nonneg (p : E → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (ω : ConfigSpace E) :
    0 ≤ configWeightV p ω := by
  unfold configWeightV edgeWeightV
  apply Finset.prod_nonneg
  intro e _
  by_cases h : ω e = true
  · rw [if_pos h]; exact (hp e).1
  · rw [if_neg h]; linarith [(hp e).2]


lemma pivotalProbV_nonneg (p : E → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
    (A : Set (ConfigSpace E)) (e : E) : 0 ≤ pivotalProbV p A e := by
  unfold pivotalProbV
  apply Finset.sum_nonneg
  intro ω _
  apply mul_nonneg _ (configWeightV_nonneg p hp ω)
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω


end Sharpness
end StatMech
