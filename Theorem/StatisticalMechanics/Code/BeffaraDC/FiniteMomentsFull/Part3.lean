/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMomentsFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.StochasticDomination
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Theorem.StatisticalMechanics.Code.FK.ComparisonHolley.Part3
import Theorem.StatisticalMechanics.Code.FK.HolleyCoupling.Part2
import Theorem.StatisticalMechanics.Code.BeffaraDC.ClusterMoments.Part3
import Def.StatisticalMechanics.Code.BeffaraDC.FiniteMomentsFull.Part3
open scoped BigOperators
open MeasureTheory


namespace StatMech

namespace BeffaraDC

open StatMech.FK StatMech

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem fkClusterSizeTail_nonneg (p q : ℝ) (x : V) (N : ℕ) :
    0 ≤ fkClusterSizeTail G p q x N :=
  measureReal_nonneg


theorem fkClusterSizeLargeEvent_eq_empty_of_card_lt (x : V) {N : ℕ}
    (hN : Fintype.card V < N) : fkClusterSizeLargeEvent G x N = ∅ := by
  ext ω
  simp only [fkClusterSizeLargeEvent, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
    not_le]
  exact lt_of_le_of_lt (le_trans (Finset.card_le_card (Finset.subset_univ _))
    (le_of_eq (Finset.card_univ))) hN


theorem fkClusterSizeTail_eq_zero_of_card_lt (p q : ℝ) (x : V) {N : ℕ}
    (hN : Fintype.card V < N) : fkClusterSizeTail G p q x N = 0 := by
  unfold fkClusterSizeTail
  rw [fkClusterSizeLargeEvent_eq_empty_of_card_lt G x hN, measureReal_empty]


theorem fkClusterSizeTail_le_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (x : V) (N : ℕ) : fkClusterSizeTail G p q x N ≤ 1 := by
  haveI : IsProbabilityMeasure (measOfMass (fkProb G p q)) :=
    measOfMass_isProbabilityMeasure (fkProb G p q)
      (fun ω => fkProb_nonneg G hp hp1 hq ω) (fkProb_sum_eq_one G hp hp1 hq)
  exact measureReal_le_one (μ := measOfMass (fkProb G p q))
    (s := fkClusterSizeLargeEvent G x N)


theorem fkClusterSizeTail_le_bernoulli {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (x : V) (N : ℕ) :
    fkClusterSizeTail G p q x N ≤ fkClusterSizeTail G p 1 x N :=
  fk_le_bernoulli G hp hp1 hq (fkClusterSizeLargeEvent G x N)
    (measurableSet_fkClusterSizeLargeEvent G x N)
    (fkClusterSizeLargeEvent_isIncreasing G x N)


theorem fkClusterSizeTail_geometricTail {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (x : V) {C r : ℝ} (hbtail : ∀ N, fkClusterSizeTail G p 1 x N ≤ C * r ^ N) :
    ∀ N, fkClusterSizeTail G p q x N ≤ C * r ^ N :=
  fun N => (fkClusterSizeTail_le_bernoulli G hp hp1 hq x N).trans (hbtail N)


theorem exists_geometricTail {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (x : V) :
    ∃ C r, 0 ≤ r ∧ r < 1 ∧ ∀ N, fkClusterSizeTail G p q x N ≤ C * r ^ N := by
  refine ⟨(2 : ℝ) ^ (Fintype.card V + 1), 1 / 2, by norm_num, by norm_num, fun N => ?_⟩
  by_cases hN : Fintype.card V < N
  · rw [fkClusterSizeTail_eq_zero_of_card_lt G p q x hN]
    positivity
  · rw [not_lt] at hN
    refine (fkClusterSizeTail_le_one G hp hp1 hq x N).trans ?_
    
    have h2 : (2 : ℝ) ^ (Fintype.card V + 1) * (1 / 2) ^ N
        = (2 : ℝ) ^ (Fintype.card V + 1) / (2 : ℝ) ^ N := by
      rw [div_pow, one_pow]; ring
    rw [h2, le_div_iff₀ (by positivity)]
    have hle : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ (Fintype.card V + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith [hle, pow_pos (show (0:ℝ) < 2 by norm_num) (Fintype.card V + 1)]


end BeffaraDC
end StatMech
