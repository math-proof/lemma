/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BKKKLLevel2Prove.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.BKKKLMeanInfl.Part2
open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem bkt2p_undegree_le_var {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool)
    {u' : ℝ} (hu'0 : 0 ≤ u') (hu'1 : u' < 1) (k : ℕ) :
    ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
        (1 - u') ^ S.card * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  set f := fun ω : ConfigSpace ι => if φ ω then (1 : ℝ) else 0 with hf
  set μ := OSSS.expect (OSSS.bernoulliWeight p) f with hμ
  have h1u'0 : (0 : ℝ) ≤ 1 - u' := by linarith
  have h1u'1 : (1 : ℝ) - u' ≤ 1 := by linarith
  
  have hvarF : μ * (1 - μ) = ∑ S ∈ (univ.erase (∅ : Finset ι)), (ptn_coeff p f S) ^ 2 := by
    rw [← ptn_var_eq_fourierWeight hp0 hp1 f, mil_var_eq φ, ← hμ]; ring
  rw [hvarF]
  calc ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
          (1 - u') ^ S.card * (ptn_coeff p f S) ^ 2
      ≤ ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
          (ptn_coeff p f S) ^ 2 := by
        apply Finset.sum_le_sum
        intro S _
        have hpow : (1 - u') ^ S.card ≤ 1 := pow_le_one₀ h1u'0 h1u'1
        nlinarith [hpow, sq_nonneg (ptn_coeff p f S), pow_nonneg h1u'0 S.card]
    _ ≤ ∑ S ∈ (univ.erase (∅ : Finset ι)), (ptn_coeff p f S) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro S hS
          rw [Finset.mem_filter] at hS
          rw [Finset.mem_erase]
          refine ⟨?_, Finset.mem_univ S⟩
          intro he; rw [he, Finset.card_empty] at hS; omega
        · intro S _ _; positivity


theorem bkt2p_levelGe2_le_var {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (φ : ConfigSpace ι → Bool)
    {u u' : ℝ} (hu1 : u < 1) (hu'0 : 0 ≤ u') (hlt : u' < u) (k : ℕ) :
    4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
        (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ (4 / (u - u'))
        * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
            * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))) := by
  have hu'1 : u' < 1 := by linarith
  have hdpos : 0 < u - u' := by linarith
  
  have hlever := bkt2f_degreeWeight_le_undegree (p := p) hu1 hlt φ k
  
  have hvar := bkt2p_undegree_le_var hp0 hp1 φ hu'0 hu'1 k
  
  calc 4 * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
          (S.card : ℝ) * (1 - u) ^ (S.card - 1)
            * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2
      ≤ 4 * ((1 / (u - u')) * ∑ S ∈ univ.filter (fun S : Finset ι => 2 ≤ S.card ∧ S.card ≤ k),
          (1 - u') ^ S.card * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) :=
        mul_le_mul_of_nonneg_left hlever (by norm_num)
    _ ≤ 4 * ((1 / (u - u'))
          * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
              * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_left hvar
        positivity
    _ = (4 / (u - u'))
          * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
              * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))) := by
        ring


end StatMech.Probability
