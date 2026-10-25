/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SourceCurrentTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.LocalCurrentTail.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.Claim1IsingComplete.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part4
import Def.StatisticalMechanics.Code.FrontierB.SourceCurrentTail
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem currentWeight_le_currentSum_of_sources
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (A : Finset V) (m : EdgeCurrent G)
    (hm : sources G (ofEdgeFun G m) = A) :
    weight G beta J (ofEdgeFun G m) ≤ currentSum G beta J A := by
  unfold currentSum
  have hs := (summable_norm_currentSum_summand G beta J A).of_norm
  calc
    weight G beta J (ofEdgeFun G m) =
        (if sources G (ofEdgeFun G m) = A then
          weight G beta J (ofEdgeFun G m) else 0) := by simp [hm]
    _ ≤ ∑' n : EdgeCurrent G,
        if sources G (ofEdgeFun G n) = A then
          weight G beta J (ofEdgeFun G n) else 0 :=
      hs.le_tsum m (fun n _ => currentSummand_nonneg G beta J hbeta hJ A n)


theorem currentSum_empty_le_unrestricted
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e) :
    currentSum G beta J ∅ ≤
      Real.exp (∑ e ∈ G.edgeFinset, beta * J e) := by
  rw [← unrestricted_current_mass G beta J hbeta hJ]
  unfold currentSum
  have hs := (summable_norm_currentSum_summand G beta J ∅).of_norm
  have hu := (summable_norm_weight_ofEdgeFun G beta J).of_norm
  apply hs.tsum_le_tsum
  · intro m
    by_cases hsrc : sources G (ofEdgeFun G m) = ∅
    · simp [hsrc]
    · simp [hsrc, currentWeight_nonneg G beta J hbeta hJ m]
  · exact hu


theorem currentWitness_correlation_lower_bound
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (A : Finset V) (m : EdgeCurrent G)
    (hm : sources G (ofEdgeFun G m) = A) :
    weight G beta J (ofEdgeFun G m) /
        Real.exp (∑ e ∈ G.edgeFinset, beta * J e) ≤
      expectationJ G beta J A := by
  have hw := currentWeight_le_currentSum_of_sources
    G beta J hbeta hJ A m hm
  have hzero := currentSum_empty_le_unrestricted G beta J hbeta hJ
  have hcorr : 0 ≤ expectationJ G beta J A :=
    Ising.acr_expectationJ_nonneg G beta J hbeta hJ A
  have hscaled : weight G beta J (ofEdgeFun G m) ≤
      expectationJ G beta J A *
        Real.exp (∑ e ∈ G.edgeFinset, beta * J e) := by
    calc
      weight G beta J (ofEdgeFun G m) ≤ currentSum G beta J A := hw
      _ = expectationJ G beta J A * currentSum G beta J ∅ :=
        Ising.acr_eq15_insertion' G beta J A
      _ ≤ expectationJ G beta J A *
          Real.exp (∑ e ∈ G.edgeFinset, beta * J e) :=
        mul_le_mul_of_nonneg_left hzero hcorr
  exact (div_le_iff₀ (Real.exp_pos _)).2 hscaled


theorem localCurrentWitness_correlation_lower_bound
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (S A : Finset V) (m : EdgeCurrent G)
    (hm : sources G (ofEdgeFun G m) = A) :
    weight G beta (couplingIn J S) (ofEdgeFun G m) /
        Real.exp (∑ e ∈ G.edgeFinset, beta * couplingIn J S e) ≤
      expectationJ G beta J A := by
  calc
    weight G beta (couplingIn J S) (ofEdgeFun G m) /
        Real.exp (∑ e ∈ G.edgeFinset, beta * couplingIn J S e) ≤
        expectationJ G beta (couplingIn J S) A :=
      currentWitness_correlation_lower_bound G beta (couplingIn J S)
        hbeta (fun e => by
          unfold couplingIn
          split
          · exact hJ e
          · exact le_rfl) A m hm
    _ ≤ expectationJ G beta J A :=
      expectationJ_couplingIn_le G beta J hbeta hJ S A


theorem currentWeight_pos
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 < beta) (hJ : ∀ e ∈ G.edgeFinset, 0 < J e)
    (m : EdgeCurrent G) :
    0 < weight G beta J (ofEdgeFun G m) := by
  unfold weight
  apply Finset.prod_pos
  intro e he
  exact div_pos (pow_pos (mul_pos hbeta (hJ e he)) _)
    (by positivity)


theorem currentWeight_pos_of_positive_on_support
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 < beta)
    (m : EdgeCurrent G)
    (hJ : ∀ e : G.edgeFinset, m e ≠ 0 → 0 < J e.1) :
    0 < weight G beta J (ofEdgeFun G m) := by
  unfold weight
  apply Finset.prod_pos
  intro e he
  by_cases hm : m ⟨e, he⟩ = 0
  · simp [ofEdgeFun, he, hm]
  · simp only [ofEdgeFun, dif_pos he]
    exact div_pos (pow_pos (mul_pos hbeta (hJ ⟨e, he⟩ hm)) _)
      (by positivity)


end StatMech.FrontierB
