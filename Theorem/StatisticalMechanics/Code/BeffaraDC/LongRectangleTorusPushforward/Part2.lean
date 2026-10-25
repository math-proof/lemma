/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusCover.Part6
import Theorem.StatisticalMechanics.Code.FK.FKG
import Instance.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager

open StatMech.Universality


theorem torusAmbientMeasure_singleton (L : ℕ) [Fact (2 < L)]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : TorusAmbientConfig L) :
    torusAmbientMeasure L hp hp1 hq {omega} =
      ENNReal.ofReal (torusAmbientProbability L p q omega) := by
  unfold torusAmbientMeasure
  rw [PMF.toMeasure_apply_singleton _ omega (measurableSet_singleton omega),
    torusAmbientPMF_apply]


theorem torusAmbientProbability_nonneg (L : ℕ) [Fact (2 < L)]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : TorusAmbientConfig L) :
    0 ≤ torusAmbientProbability L p q omega :=
  (div_pos (torusAmbientFKWeight_pos L omega hp hp1 hq)
    (torusAmbientPartition_pos L hp hp1 hq)).le


theorem torusAmbientMeasure_real_eq_indicator_sum
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (TorusAmbientConfig L)) :
    (torusAmbientMeasure L hp hp1 hq).real A =
      ∑ omega : TorusAmbientConfig L,
        torusAmbientProbability L p q omega *
          A.indicator (fun _ => (1 : ℝ)) omega := by
  rw [Measure.real, torusAmbientMeasure, PMF.toMeasure_apply_fintype]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro omega _homega
    by_cases hmem : omega ∈ A
    · simp only [Set.indicator_of_mem hmem, torusAmbientPMF_apply]
      rw [ENNReal.toReal_ofReal
        (torusAmbientProbability_nonneg L hp hp1 hq omega)]
      simp
    · simp [Set.indicator, hmem]
  · intro omega _homega
    by_cases hmem : omega ∈ A <;>
      simp [Set.indicator, hmem, torusAmbientPMF_apply]


theorem torusAmbientConfigExtend_sup
    (L : ℕ) [Fact (2 < L)] (omega eta : TorusAmbientConfig L) :
    torusAmbientConfigExtend L (omega ⊔ eta) =
      torusAmbientConfigExtend L omega ⊔
        torusAmbientConfigExtend L eta := by
  funext e
  by_cases he : e ∈ (onsTorusGraph L).edgeFinset <;>
    simp [torusAmbientConfigExtend, he]


theorem torusAmbientConfigExtend_inf
    (L : ℕ) [Fact (2 < L)] (omega eta : TorusAmbientConfig L) :
    torusAmbientConfigExtend L (omega ⊓ eta) =
      torusAmbientConfigExtend L omega ⊓
        torusAmbientConfigExtend L eta := by
  funext e
  by_cases he : e ∈ (onsTorusGraph L).edgeFinset <;>
    simp [torusAmbientConfigExtend, he]


theorem torusAmbientFKWeight_logSupermodular
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (omega eta : TorusAmbientConfig L) :
    torusAmbientFKWeight L p q omega *
        torusAmbientFKWeight L p q eta ≤
      torusAmbientFKWeight L p q (omega ⊔ eta) *
        torusAmbientFKWeight L p q (omega ⊓ eta) := by
  unfold torusAmbientFKWeight
  rw [torusAmbientConfigExtend_sup, torusAmbientConfigExtend_inf]
  exact FK.fkWeight_logSupermodular (onsTorusGraph L) hp hp1 hq _ _


theorem torusAmbientProbability_FKGLatticeCondition
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    FKGLatticeCondition (torusAmbientProbability L p q) := by
  have hZpos : 0 < torusAmbientPartition L p q :=
    torusAmbientPartition_pos L hp hp1
      (lt_of_lt_of_le zero_lt_one hq)
  intro omega eta
  simp only [torusAmbientProbability]
  rw [div_mul_div_comm, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right (mul_pos hZpos hZpos)).mpr
    (torusAmbientFKWeight_logSupermodular L hp hp1 hq omega eta)


theorem torusAmbientMeasure_positivelyAssociated
    (L : ℕ) [Fact (2 < L)] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq : 1 ≤ q) :
    PositivelyAssociated (torusAmbientMeasure L hp hp1 hq0) := by
  intro A B hA hB
  rw [torusAmbientMeasure_real_eq_indicator_sum,
    torusAmbientMeasure_real_eq_indicator_sum,
    torusAmbientMeasure_real_eq_indicator_sum]
  exact fkg_inequality_events
    (torusAmbientProbability_nonneg L hp hp1 hq0)
    (torusAmbientProbability_sum_one L hp hp1 hq0)
    (torusAmbientProbability_FKGLatticeCondition L hp hp1 hq)
    hA hB


end StatMech.BeffaraDC
