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
import Def.StatisticalMechanics.Code.FrontierB.SourceCurrentTail.Part3
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem pathCorrelationConstant_pos {u v : V}
    (beta : ℝ) (J : Sym2 V → ℝ) (S : Finset V)
    (p : G.Walk u v) (hbeta : 0 < beta)
    (hJ : ∀ e ∈ G.edgeFinset, 0 < J e)
    (hS : ∀ x ∈ p.support, x ∈ S) :
    0 < pathCorrelationConstant G beta J S p := by
  unfold pathCorrelationConstant
  apply div_pos
  · apply currentWeight_pos_of_positive_on_support G beta
      (couplingIn J S) hbeta (pathEdgeCurrent G p)
    intro e hm
    have hePath : e.1 ∈ p.edges.toFinset := by
      by_contra he
      exact hm (by simp [pathEdgeCurrent, he])
    have heList : e.1 ∈ p.edges := by simpa using hePath
    have hins : edgeInside S e.1 := by
      intro x hx
      exact hS x (p.mem_support_of_mem_edges heList hx)
    simp [couplingIn, hins, hJ e.1 e.2]
  · exact Real.exp_pos _


theorem pathCorrelationConstant_le_expectation {u v : V}
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ e, 0 ≤ J e)
    (S : Finset V) (p : G.Walk u v)
    (hp : p.IsPath) (huv : u ≠ v) :
    pathCorrelationConstant G beta J S p ≤
      expectationJ G beta J {u, v} := by
  unfold pathCorrelationConstant
  exact localCurrentWitness_correlation_lower_bound G beta J hbeta hJ
    S {u, v} (pathEdgeCurrent G p) (sources_pathEdgeCurrent G p hp huv)


theorem currentSum_pair_pos_of_path {u v : V}
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 < beta) (hJ : ∀ e, 0 < J e)
    (p : G.Walk u v) (hp : p.IsPath) (huv : u ≠ v) :
    0 < currentSum G beta J {u, v} := by
  exact lt_of_lt_of_le
    (currentWeight_pos G beta J hbeta (fun e _ => hJ e)
      (pathEdgeCurrent G p))
    (currentWeight_le_currentSum_of_sources G beta J hbeta.le
      (fun e => (hJ e).le)
      {u, v} (pathEdgeCurrent G p) (sources_pathEdgeCurrent G p hp huv))


theorem source_current_tail_doubling_le
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ f, 0 ≤ J f)
    (A : Finset V) (e : G.edgeFinset) (K : ℕ) :
    (∑' m : EdgeCurrent G,
        if sources G (ofEdgeFun G m) = A ∧ K ≤ m e then
          weight G beta J (ofEdgeFun G m) else 0) ≤
      ((2 : ℝ) ^ K)⁻¹ *
        currentSum G beta (doubledEdgeCoupling J e.1) A := by
  let tail : EdgeCurrent G → ℝ := fun m =>
    if sources G (ofEdgeFun G m) = A ∧ K ≤ m e then
      weight G beta J (ofEdgeFun G m) else 0
  let major : EdgeCurrent G → ℝ := fun m =>
    ((2 : ℝ) ^ K)⁻¹ *
      (if sources G (ofEdgeFun G m) = A then
        weight G beta (doubledEdgeCoupling J e.1) (ofEdgeFun G m) else 0)
  have hJ' : ∀ f, 0 ≤ doubledEdgeCoupling J e.1 f :=
    doubledEdgeCoupling_nonneg J hJ e.1
  have htail_nonneg : ∀ m, 0 ≤ tail m := by
    intro m
    simp only [tail]
    split
    · exact currentWeight_nonneg G beta J hbeta hJ _
    · exact le_rfl
  have hmajor : Summable major := by
    exact ((summable_norm_currentSum_summand G beta
      (doubledEdgeCoupling J e.1) A).of_norm).mul_left (((2 : ℝ) ^ K)⁻¹)
  have hpoint : ∀ m, tail m ≤ major m := by
    intro m
    simp only [tail, major]
    by_cases hsrc : sources G (ofEdgeFun G m) = A
    · by_cases hm : K ≤ m e
      · simp only [hsrc, hm, and_self, if_true]
        rw [weight_doubledEdgeCoupling G beta J e m]
        have hpow : (2 : ℝ) ^ K ≤ (2 : ℝ) ^ m e :=
          pow_le_pow_right₀ (by norm_num) hm
        have hpos : 0 < (2 : ℝ) ^ K := by positivity
        rw [inv_mul_eq_div]
        apply (le_div_iff₀ hpos).2
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right hpow
          (currentWeight_nonneg G beta J hbeta hJ _)
      · simp [hsrc, hm,
          currentWeight_nonneg G beta (doubledEdgeCoupling J e.1) hbeta hJ']
    · simp [hsrc]
  calc
    (∑' m : EdgeCurrent G,
        if sources G (ofEdgeFun G m) = A ∧ K ≤ m e then
          weight G beta J (ofEdgeFun G m) else 0) = ∑' m, tail m := rfl
    _ ≤ ∑' m, major m :=
      (Summable.of_nonneg_of_le htail_nonneg hpoint hmajor).tsum_le_tsum hpoint hmajor
    _ = ((2 : ℝ) ^ K)⁻¹ *
        currentSum G beta (doubledEdgeCoupling J e.1) A := by
      rw [show (∑' m, major m) = ((2 : ℝ) ^ K)⁻¹ *
          ∑' m : EdgeCurrent G,
            if sources G (ofEdgeFun G m) = A then
              weight G beta (doubledEdgeCoupling J e.1) (ofEdgeFun G m) else 0 by
        exact tsum_mul_left]
      rfl


theorem currentSum_doubledEdgeCoupling_source_le
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ f, 0 ≤ J f)
    (A : Finset V) (e : G.edgeFinset)
    (c : ℝ) (hc : 0 < c)
    (hcorr : c ≤ expectationJ G beta J A) :
    currentSum G beta (doubledEdgeCoupling J e.1) A ≤
      (Real.exp (beta * J e.1) / c) * currentSum G beta J A := by
  have hJ' : ∀ f, 0 ≤ doubledEdgeCoupling J e.1 f :=
    doubledEdgeCoupling_nonneg J hJ e.1
  have hsourceDoubled :
      currentSum G beta (doubledEdgeCoupling J e.1) A ≤
        currentSum G beta (doubledEdgeCoupling J e.1) ∅ :=
    currentSum_le_empty G beta (doubledEdgeCoupling J e.1) hbeta hJ' A
  have hemptyDoubled :=
    currentSum_doubledEdgeCoupling_le G beta J hbeta hJ e
  have hsourceLower :
      c * currentSum G beta J ∅ ≤ currentSum G beta J A := by
    rw [Ising.acr_eq15_insertion' G beta J A]
    exact mul_le_mul_of_nonneg_right hcorr
      (Ising.acr_currentSum_nonneg G beta J hbeta hJ ∅)
  have hscaled :
      c * currentSum G beta (doubledEdgeCoupling J e.1) A ≤
        Real.exp (beta * J e.1) * currentSum G beta J A := by
    calc
      c * currentSum G beta (doubledEdgeCoupling J e.1) A ≤
          c * currentSum G beta (doubledEdgeCoupling J e.1) ∅ :=
        mul_le_mul_of_nonneg_left hsourceDoubled hc.le
      _ ≤ c * (Real.exp (beta * J e.1) * currentSum G beta J ∅) :=
        mul_le_mul_of_nonneg_left hemptyDoubled hc.le
      _ = Real.exp (beta * J e.1) *
          (c * currentSum G beta J ∅) := by ring
      _ ≤ Real.exp (beta * J e.1) * currentSum G beta J A :=
        mul_le_mul_of_nonneg_left hsourceLower (Real.exp_pos _).le
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).2
  simpa [mul_comm] using hscaled


theorem sourceCurrentMeasure_edge_exponential_tail_le
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ f, 0 ≤ J f)
    (A : Finset V) (hA : 0 < currentSum G beta J A)
    (e : G.edgeFinset) (c : ℝ) (hc : 0 < c)
    (hcorr : c ≤ expectationJ G beta J A) (K : ℕ) :
    (sourceCurrentMeasure G beta J hbeta hJ A hA : Measure (EdgeCurrent G))
        {m | K ≤ m e} ≤
      ENNReal.ofReal
        (Real.exp (beta * J e.1) / (c * (2 : ℝ) ^ K)) := by
  let tail : EdgeCurrent G → ℝ := fun m =>
    if sources G (ofEdgeFun G m) = A ∧ K ≤ m e then
      weight G beta J (ofEdgeFun G m) else 0
  have htail_nonneg : ∀ m, 0 ≤ tail m := by
    intro m
    simp only [tail]
    split
    · exact currentWeight_nonneg G beta J hbeta hJ _
    · exact le_rfl
  have htailSummable : Summable tail := by
    refine Summable.of_nonneg_of_le htail_nonneg (fun m => ?_)
      (summable_norm_weight_ofEdgeFun G beta J).of_norm
    simp only [tail]
    split
    · exact le_rfl
    · exact currentWeight_nonneg G beta J hbeta hJ m
  change (currentPMF G beta J hbeta hJ A hA).toMeasure {m | K ≤ m e} ≤ _
  rw [PMF.toMeasure_apply_eq_tsum]
  have hsum :
      (∑' m : EdgeCurrent G,
        {m : EdgeCurrent G | K ≤ m e}.indicator
          (currentPMF G beta J hbeta hJ A hA) m) =
        ENNReal.ofReal (∑' m, tail m) /
          ENNReal.ofReal (currentSum G beta J A) := by
    calc
      (∑' m : EdgeCurrent G,
          {m : EdgeCurrent G | K ≤ m e}.indicator
            (currentPMF G beta J hbeta hJ A hA) m) =
          ∑' m : EdgeCurrent G,
            ENNReal.ofReal (tail m) *
              (ENNReal.ofReal (currentSum G beta J A))⁻¹ := by
        apply tsum_congr
        intro m
        by_cases hm : K ≤ m e
        · rw [Set.indicator_of_mem
            (show m ∈ {m : EdgeCurrent G | K ≤ m e} from hm)]
          rw [currentPMF_apply]
          by_cases hsrc : sources G (ofEdgeFun G m) = A
          · simp [currentRawMass, tail, hsrc, hm]
          · simp [currentRawMass, tail, hsrc]
        · rw [Set.indicator_of_notMem
            (show m ∉ {m : EdgeCurrent G | K ≤ m e} from hm)]
          simp [tail, hm]
      _ = (∑' m : EdgeCurrent G, ENNReal.ofReal (tail m)) *
          (ENNReal.ofReal (currentSum G beta J A))⁻¹ := ENNReal.tsum_mul_right
      _ = ENNReal.ofReal (∑' m, tail m) *
          (ENNReal.ofReal (currentSum G beta J A))⁻¹ := by
        rw [ENNReal.ofReal_tsum_of_nonneg htail_nonneg htailSummable]
      _ = ENNReal.ofReal (∑' m, tail m) /
          ENNReal.ofReal (currentSum G beta J A) := rfl
  rw [hsum]
  rw [ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hA).ne' ENNReal.ofReal_ne_top]
  have hcoef : 0 ≤ Real.exp (beta * J e.1) / (c * (2 : ℝ) ^ K) :=
    div_nonneg (Real.exp_pos _).le (mul_nonneg hc.le (pow_nonneg (by norm_num) _))
  rw [← ENNReal.ofReal_mul hcoef]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∑' m, tail m) ≤ ((2 : ℝ) ^ K)⁻¹ *
        currentSum G beta (doubledEdgeCoupling J e.1) A :=
      source_current_tail_doubling_le G beta J hbeta hJ A e K
    _ ≤ ((2 : ℝ) ^ K)⁻¹ *
        ((Real.exp (beta * J e.1) / c) * currentSum G beta J A) :=
      mul_le_mul_of_nonneg_left
        (currentSum_doubledEdgeCoupling_source_le
          G beta J hbeta hJ A e c hc hcorr)
        (inv_nonneg.2 (pow_nonneg (by norm_num) _))
    _ = (Real.exp (beta * J e.1) / (c * (2 : ℝ) ^ K)) *
        currentSum G beta J A := by field_simp


theorem sourceCurrentMeasure_edge_inverse_tail_le
    (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 ≤ beta) (hJ : ∀ f, 0 ≤ J f)
    (A : Finset V) (hA : 0 < currentSum G beta J A)
    (e : G.edgeFinset) (c : ℝ) (hc : 0 < c)
    (hcorr : c ≤ expectationJ G beta J A)
    (K : ℕ) (hK : 0 < K) :
    (sourceCurrentMeasure G beta J hbeta hJ A hA : Measure (EdgeCurrent G))
        {m | K ≤ m e} ≤
      ENNReal.ofReal (Real.exp (beta * J e.1) / (c * K)) := by
  calc
    (sourceCurrentMeasure G beta J hbeta hJ A hA : Measure (EdgeCurrent G))
        {m | K ≤ m e} ≤
        ENNReal.ofReal
          (Real.exp (beta * J e.1) / (c * (2 : ℝ) ^ K)) :=
      sourceCurrentMeasure_edge_exponential_tail_le
        G beta J hbeta hJ A hA e c hc hcorr K
    _ ≤ ENNReal.ofReal (Real.exp (beta * J e.1) / (c * K)) := by
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_left (Real.exp_pos _).le
        (mul_pos hc (Nat.cast_pos.2 hK))
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast nat_le_two_pow K) hc.le

end StatMech.FrontierB
