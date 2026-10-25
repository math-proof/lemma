/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.STT.Part4
import Def.StatisticalMechanics.Code.Universality.STTFull.Part2
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

theorem stt_starMass_ne_top (p0 p1 p2 : ℝ) (c : Bool × Bool × Bool) :
    stt_starMass p0 p1 p2 c ≠ ⊤ := by
  unfold stt_starMass stt_triW
  rw [← lt_top_iff_ne_top]
  apply ENNReal.sum_lt_top.2
  intro ω _
  by_cases h : stt_starConn ω = c <;> simp [h]


theorem stt_mass_eq (p0 p1 p2 : ℝ)
    (h0 : 0 ≤ p0) (h0' : p0 ≤ 1) (h1 : 0 ≤ p1) (h1' : p1 ≤ 1) (h2 : 0 ≤ p2) (h2' : p2 ≤ 1)
    (h : IsCriticalTri p0 p1 p2) (c : Bool × Bool × Bool) :
    stt_triMass p0 p1 p2 c = stt_starMass (1 - p0) (1 - p1) (1 - p2) c := by
  unfold stt_triMass stt_starMass stt_triW
  rw [stt_ennreal_sum_ofReal_indicator (localWeight p0 p1 p2) (fun ω => stt_triConn ω = c)
        (stt_localWeight_nonneg p0 p1 p2 h0 h0' h1 h1' h2 h2'),
      stt_ennreal_sum_ofReal_indicator (localWeight (1 - p0) (1 - p1) (1 - p2))
        (fun ω => stt_starConn ω = c)
        (stt_localWeight_nonneg (1 - p0) (1 - p1) (1 - p2) (by linarith) (by linarith)
          (by linarith) (by linarith) (by linarith) (by linarith))]
  rw [stt_connWeight_eq p0 p1 p2 h c]


theorem stt_triLocalMeasure_singleton (p0 p1 p2 : ℝ) (ω0 : LocalConfig) :
    stt_triLocalMeasure p0 p1 p2 {ω0} = stt_triW p0 p1 p2 ω0 := by
  unfold stt_triLocalMeasure stt_triW
  rw [Measure.coe_finsetSum, Finset.sum_apply, Finset.sum_eq_single ω0]
  · rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton ω0)]
    simp
  · intro ω _ hne
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton ω0)]
    simp [Set.indicator, hne]
  · intro hns; exact absurd (Finset.mem_univ ω0) hns


end Universality
end StatMech
