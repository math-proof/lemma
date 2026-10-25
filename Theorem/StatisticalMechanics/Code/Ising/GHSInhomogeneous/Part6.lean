/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomVertexPartition.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeSum
import Theorem.StatisticalMechanics.Code.Sharpness.GHSConcavity
import Def.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part5
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option maxHeartbeats 2400000


namespace StatMech.Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ghsiDisagreementCorr_antitone (K : Sym2 V → ℝ)
    (hK : ∀ e, 0 ≤ K e) (o x : V) :
    Antitone (ghsiDisagreementCorr G K o x) := by
  intro A B hAB
  by_cases hA : o ∈ A ∨ x ∈ A
  · have hB : o ∈ B ∨ x ∈ B := hA.elim (fun ho => Or.inl (hAB ho))
      (fun hx => Or.inr (hAB hx))
    simp [ghsiDisagreementCorr, hA, hB]
  · by_cases hB : o ∈ B ∨ x ∈ B
    · simp only [ghsiDisagreementCorr, if_pos hB, if_neg hA]
      apply ghsvp_vertexCorr_nonneg
      intro e
      exact mul_nonneg (by norm_num) (hK e)
    · simp only [ghsiDisagreementCorr, if_neg hA, if_neg hB]
      apply ghsvp_vertexCorr_mono
      · intro e
        exact mul_nonneg (by norm_num) (hK e)
      · exact fun e he => SimpleGraph.not_isDiag_of_mem_edgeFinset he
      · intro v hv
        simp only [Finset.mem_compl] at hv ⊢
        exact fun hvA => hv (hAB hvA)

theorem ghsiAgreementMag_monotone (K : Sym2 V → ℝ) (hf : V → ℝ)
    (hK : ∀ e, 0 ≤ K e) (hhf : ∀ x, 0 ≤ hf x) (y : V) :
    Monotone (ghsiAgreementMag G K hf y) := by
  intro A B hAB
  by_cases hB : y ∈ B
  · by_cases hA : y ∈ A
    · simp only [ghsiAgreementMag, if_pos hA, if_pos hB]
      apply ghsvp_vertexCorrField_mono
      · intro e
        exact mul_nonneg (by norm_num) (hK e)
      · intro v
        exact mul_nonneg (by norm_num) (hhf v)
      · exact fun e he => SimpleGraph.not_isDiag_of_mem_edgeFinset he
      · exact hAB
    · simp only [ghsiAgreementMag, if_neg hA, if_pos hB]
      apply ghsvp_vertexCorrField_nonneg
      · intro e
        exact mul_nonneg (by norm_num) (hK e)
      · intro v
        exact mul_nonneg (by norm_num) (hhf v)
  · have hA : y ∉ A := fun hy => hB (hAB hy)
    simp [ghsiAgreementMag, hA, hB]

theorem ghsiFibreUU_eq_disagreementCorr (K : Sym2 V → ℝ) (hf : V → ℝ)
    (o x : V) (hox : o ≠ x) (q : ConfigSpace V) :
    ghsiFibreUU G K hf o x q =
      ghsiDisagreementCorr G K o x (ghsLAgreeFinset q) := by
  rw [ghsiFibreUU_eq_uExpectation]
  by_cases ho : o ∈ ghsLAgreeFinset q
  · have hqo : q o = true := (mem_ghsLAgreeFinset q o).mp ho
    unfold ghsiUExpectation ghsiDisagreementCorr
    rw [if_pos (Or.inl ho)]
    simp_rw [ghsL_uvar_mate, if_pos hqo, zero_mul, mul_zero]
    simp
  · by_cases hx : x ∈ ghsLAgreeFinset q
    · have hqx : q x = true := (mem_ghsLAgreeFinset q x).mp hx
      unfold ghsiUExpectation ghsiDisagreementCorr
      rw [if_pos (Or.inr hx)]
      simp_rw [ghsL_uvar_mate, if_pos hqx, mul_zero]
      simp
    · have hqo : ¬ q o = true := fun h => ho ((mem_ghsLAgreeFinset q o).mpr h)
      have hqx : ¬ q x = true := fun h => hx ((mem_ghsLAgreeFinset q x).mpr h)
      unfold ghsiUExpectation ghsiDisagreementCorr ghsvp_vertexCorr expJ
      rw [if_neg (not_or_intro ho hx)]
      apply congrArg₂ (· / ·)
      · apply Finset.sum_congr rfl
        intro a _
        rw [ghsiUWeight_eq_wJ]
        simp only [ghsL_uvar_mate, if_neg hqo, if_neg hqx]
        unfold spinProd
        rw [Finset.prod_pair hox]
        ring
      · apply Finset.sum_congr rfl
        intro a _
        rw [ghsiUWeight_eq_wJ]


end StatMech.Ising
