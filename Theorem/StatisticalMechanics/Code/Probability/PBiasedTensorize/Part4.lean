/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedConvexity.Part2
import Theorem.StatisticalMechanics.Code.Probability.KKLpBiased.Part2
import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseClose2
import Def.StatisticalMechanics.Code.Probability.PBiasedTensorize.Part4
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem ptn_pchar_empty (p : ℝ) (ω : ConfigSpace ι) :
    ptn_pchar p (∅ : Finset ι) ω = 1 := by simp [ptn_pchar]


theorem ptn_pchar_as_univ (p : ℝ) (S : Finset ι) (ω : ConfigSpace ι) :
    ptn_pchar p S ω = ∏ i : ι, (if i ∈ S then ptn_psi p (ω i) else 1) := by
  unfold ptn_pchar; rw [Finset.prod_ite_mem, Finset.univ_inter]


theorem ptn_orthonormal {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (S T : Finset ι) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => ptn_pchar p S ω * ptn_pchar p T ω)
      = if S = T then 1 else 0 := by
  have hmean := ptn_psi_mean hp0 hp1
  have hsq := ptn_psi_sq_mean hp0 hp1
  
  have hprod : (fun ω : ConfigSpace ι => ptn_pchar p S ω * ptn_pchar p T ω)
      = (fun ω => ∏ e : ι,
          ((if e ∈ S then ptn_psi p (ω e) else 1) * (if e ∈ T then ptn_psi p (ω e) else 1))) := by
    funext ω
    rw [ptn_pchar_as_univ, ptn_pchar_as_univ, ← Finset.prod_mul_distrib]
  rw [hprod]
  rw [ptn_expect_prod p (fun e b => (if e ∈ S then ptn_psi p b else 1) * (if e ∈ T then ptn_psi p b else 1))]
  
  have hfac : ∀ e : ι,
      (1 - p) * ((if e ∈ S then ptn_psi p false else 1) * (if e ∈ T then ptn_psi p false else 1))
        + p * ((if e ∈ S then ptn_psi p true else 1) * (if e ∈ T then ptn_psi p true else 1))
        = if e ∈ S ↔ e ∈ T then 1 else 0 := by
    intro e
    by_cases hS : e ∈ S <;> by_cases hT : e ∈ T <;>
      simp only [hS, hT, if_true, if_false, one_mul, mul_one, iff_true, iff_false,
        iff_self, not_true_eq_false]
    · 
      nlinarith [hsq]
    · 
      linarith [hmean]
    · 
      linarith [hmean]
    · 
      ring
  simp_rw [hfac]
  by_cases hST : S = T
  · subst hST
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro e _; rw [if_pos Iff.rfl]
  · rw [if_neg hST]
    
    have : ∃ e : ι, ¬ (e ∈ S ↔ e ∈ T) := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hST (Finset.ext (fun e => h e))
    obtain ⟨e, he⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ e) (by rw [if_neg he])


end StatMech.Probability
