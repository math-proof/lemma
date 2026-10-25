/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.STT.Part4
import Def.StatisticalMechanics.Code.Universality.STTFull
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

theorem stt_localWeight_nonneg (p0 p1 p2 : ℝ)
    (h0 : 0 ≤ p0) (h0' : p0 ≤ 1) (h1 : 0 ≤ p1) (h1' : p1 ≤ 1) (h2 : 0 ≤ p2) (h2' : p2 ≤ 1)
    (ω : LocalConfig) : 0 ≤ localWeight p0 p1 p2 ω := by
  unfold localWeight edgeWeight
  apply mul_nonneg; apply mul_nonneg
  · cases ω.1 <;> simp <;> linarith
  · cases ω.2.1 <;> simp <;> linarith
  · cases ω.2.2 <;> simp <;> linarith


theorem stt_sum_weighted_dirac_singleton {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [DecidableEq α]
    (g : LocalConfig → ℝ≥0∞) (f : LocalConfig → α) (a : α) :
    (∑ ω : LocalConfig, g ω • Measure.dirac (f ω)) {a}
      = ∑ ω : LocalConfig, if f ω = a then g ω else 0 := by
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton a)]
  by_cases h : f ω = a <;> simp [Set.indicator, h]


theorem stt_map_triLocalMeasure (p0 p1 p2 : ℝ) (f : LocalConfig → Bool × Bool × Bool) :
    Measure.map f (stt_triLocalMeasure p0 p1 p2)
      = ∑ ω : LocalConfig, ENNReal.ofReal (localWeight p0 p1 p2 ω) • Measure.dirac (f ω) := by
  have hf : Measurable f := measurable_of_countable f
  ext s hs
  rw [Measure.map_apply hf hs]
  unfold stt_triLocalMeasure
  rw [Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
      Measure.dirac_apply' _ (hf hs), Measure.dirac_apply' _ hs]
  congr 1


theorem stt_triLocalMeasure_univ (p0 p1 p2 : ℝ)
    (h0 : 0 ≤ p0) (h0' : p0 ≤ 1) (h1 : 0 ≤ p1) (h1' : p1 ≤ 1) (h2 : 0 ≤ p2) (h2' : p2 ≤ 1) :
    stt_triLocalMeasure p0 p1 p2 Set.univ = 1 := by
  unfold stt_triLocalMeasure
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  have : ∀ ω : LocalConfig,
      (ENNReal.ofReal (localWeight p0 p1 p2 ω) • Measure.dirac ω) Set.univ
        = ENNReal.ofReal (localWeight p0 p1 p2 ω) := by
    intro ω
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.univ]
    simp
  rw [Finset.sum_congr rfl (fun ω _ => this ω)]
  rw [← ENNReal.ofReal_sum_of_nonneg
      (fun ω _ => stt_localWeight_nonneg p0 p1 p2 h0 h0' h1 h1' h2 h2' ω)]
  rw [sum_localWeight]
  simp


theorem stt_isProbabilityMeasure_triLocalMeasure (p0 p1 p2 : ℝ)
    (h0 : 0 ≤ p0) (h0' : p0 ≤ 1) (h1 : 0 ≤ p1) (h1' : p1 ≤ 1) (h2 : 0 ≤ p2) (h2' : p2 ≤ 1) :
    IsProbabilityMeasure (stt_triLocalMeasure p0 p1 p2) :=
  ⟨stt_triLocalMeasure_univ p0 p1 p2 h0 h0' h1 h1' h2 h2'⟩


theorem stt_connWeight_eq (p0 p1 p2 : ℝ) (h : IsCriticalTri p0 p1 p2) (c : Bool × Bool × Bool) :
    (∑ ω : LocalConfig, if stt_triConn ω = c then localWeight p0 p1 p2 ω else 0)
      = ∑ ω : LocalConfig, if stt_starConn ω = c then localWeight (1-p0) (1-p1) (1-p2) ω else 0 := by
  unfold IsCriticalTri kappaTri at h
  obtain ⟨c1, c2, c3⟩ := c
  simp only [stt_triConn, stt_starConn, localWeight, edgeWeight, triAB, triAC, triBC,
    starAB, starAC, starBC, Fintype.sum_prod_type, Fintype.sum_bool, Prod.mk.injEq]
  cases c1 <;> cases c2 <;> cases c3 <;> norm_num <;> nlinarith [h]


theorem stt_ennreal_sum_ofReal_indicator (g : LocalConfig → ℝ) (P : LocalConfig → Prop)
    [DecidablePred P] (hg : ∀ ω, 0 ≤ g ω) :
    (∑ ω : LocalConfig, if P ω then ENNReal.ofReal (g ω) else 0)
      = ENNReal.ofReal (∑ ω : LocalConfig, if P ω then g ω else 0) := by
  rw [ENNReal.ofReal_sum_of_nonneg (by intro ω _; by_cases h : P ω <;> simp [h, hg ω])]
  apply Finset.sum_congr rfl
  intro ω _; by_cases h : P ω <;> simp [h]


theorem stt_map_conn_eq (p0 p1 p2 : ℝ)
    (h0 : 0 ≤ p0) (h0' : p0 ≤ 1) (h1 : 0 ≤ p1) (h1' : p1 ≤ 1) (h2 : 0 ≤ p2) (h2' : p2 ≤ 1)
    (h : IsCriticalTri p0 p1 p2) :
    Measure.map stt_triConn (stt_triLocalMeasure p0 p1 p2)
      = Measure.map stt_starConn (stt_triLocalMeasure (1 - p0) (1 - p1) (1 - p2)) := by
  rw [stt_map_triLocalMeasure, stt_map_triLocalMeasure]
  apply Measure.ext_of_singleton
  intro c
  rw [stt_sum_weighted_dirac_singleton, stt_sum_weighted_dirac_singleton,
      stt_ennreal_sum_ofReal_indicator _ _
        (stt_localWeight_nonneg p0 p1 p2 h0 h0' h1 h1' h2 h2'),
      stt_ennreal_sum_ofReal_indicator _ _
        (stt_localWeight_nonneg (1 - p0) (1 - p1) (1 - p2) (by linarith) (by linarith)
          (by linarith) (by linarith) (by linarith) (by linarith))]
  rw [stt_connWeight_eq p0 p1 p2 h c]


end Universality
end StatMech
