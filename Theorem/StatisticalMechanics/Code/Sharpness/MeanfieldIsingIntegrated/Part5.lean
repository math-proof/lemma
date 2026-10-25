/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingState.Part2
import Def.StatisticalMechanics.Code.Sharpness.MeanfieldIsingIntegrated.Part5
open MeasureTheory Real Set Filter Topology
open scoped BigOperators Interval


namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising


theorem sctMeanfieldG_tendsto_infinite
    (d : ℕ) (beta h : ℝ) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    Tendsto (fun k : ℕ => sctMeanfieldG d (k + 1) h beta)
      atTop (nhds (sctInfiniteMeanfieldG d h beta)) := by
  have hm := (sctOriginMag_tendsto_iSup d beta h hbeta hh).comp
    (tendsto_add_atTop_nat 1)
  simpa only [sctMeanfieldG, sctInfiniteMeanfieldG, sctInfiniteFieldMag]
    using tendsto_const_nhds.mul (tendsto_const_nhds.sub (hm.pow 2))


theorem sctInfiniteMeanfieldG_antitone_above
    (d : ℕ) {a b h : ℝ} (hab : a ≤ b) (ha : 0 < a) (hh : 0 < h)
    (hbdd : BddAbove (tildeBetaCIsingSet d))
    (hcrit : tildeBetaCIsing d < a) :
    sctInfiniteMeanfieldG d h b ≤ sctInfiniteMeanfieldG d h a := by
  have hb : 0 < b := ha.trans_le hab
  have hleft : Tendsto
      (fun k : ℕ =>
        sctMeanfieldG d (k + 1) h b - sctMeanfieldG d (k + 1) h a)
      atTop
      (nhds (sctInfiniteMeanfieldG d h b - sctInfiniteMeanfieldG d h a)) :=
    (sctMeanfieldG_tendsto_infinite d b h hb.le hh.le).sub
      (sctMeanfieldG_tendsto_infinite d a h ha.le hh.le)
  have hright := sctMeanfieldIntegratedError_integral_tendsto_zero
    d hab ha hh
  have hle : sctInfiniteMeanfieldG d h b - sctInfiniteMeanfieldG d h a ≤ 0 :=
    le_of_tendsto_of_tendsto hleft hright
      (Filter.Eventually.of_forall (fun k =>
        sctMeanfieldG_sub_le_integral_error
          (Nat.succ_le_succ (Nat.zero_le k)) hab ha hh hbdd hcrit))
  linarith


theorem sctInfiniteFieldMag_meanfield_lower_bound_integrated
    (d : ℕ) (hbdd : BddAbove (tildeBetaCIsingSet d))
    (hcrit : 0 < tildeBetaCIsing d) {beta h : ℝ}
    (hbeta : tildeBetaCIsing d ≤ beta) (hh : 0 < h) :
    Real.sqrt (1 - (tildeBetaCIsing d / beta) ^ 2) ≤
      sctInfiniteFieldMag d beta h := by
  have hbeta0 : 0 < beta := hcrit.trans_le hbeta
  have hm0 := sctInfiniteFieldMag_nonneg d beta h hbeta0.le hh.le
  rcases hbeta.eq_or_lt with rfl | hcritbeta
  · simpa [hcrit.ne'] using hm0
  · let a : ℕ -> ℝ := fun k =>
      tildeBetaCIsing d +
        (beta - tildeBetaCIsing d) * (1 / ((k : ℝ) + 1))
    have ha_gt (k : ℕ) : tildeBetaCIsing d < a k := by
      dsimp [a]
      have hfrac : 0 < (1 : ℝ) / ((k : ℝ) + 1) := by positivity
      nlinarith
    have ha_le (k : ℕ) : a k ≤ beta := by
      dsimp [a]
      have hfrac0 : 0 ≤ (1 : ℝ) / ((k : ℝ) + 1) := by positivity
      have hfrac1 : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        norm_num
      nlinarith
    have ha_pos (k : ℕ) : 0 < a k := hcrit.trans (ha_gt k)
    have hG : sctInfiniteMeanfieldG d h beta ≤ (tildeBetaCIsing d) ^ 2 := by
      have hbounds : ∀ k : ℕ,
          sctInfiniteMeanfieldG d h beta ≤ (a k) ^ 2 := by
        intro k
        have hanti := sctInfiniteMeanfieldG_antitone_above d
          (ha_le k) (ha_pos k) hh hbdd (ha_gt k)
        have hma0 := sctInfiniteFieldMag_nonneg d (a k) h
          (ha_pos k).le hh.le
        have hdrop : sctInfiniteMeanfieldG d h (a k) ≤ (a k) ^ 2 := by
          unfold sctInfiniteMeanfieldG
          nlinarith [sq_nonneg (sctInfiniteFieldMag d (a k) h)]
        exact hanti.trans hdrop
      have ha_tendsto : Tendsto a atTop (nhds (tildeBetaCIsing d)) := by
        have hz := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        simpa only [a, mul_zero, add_zero] using
          tendsto_const_nhds.add (tendsto_const_nhds.mul hz)
      exact le_of_tendsto_of_tendsto tendsto_const_nhds (ha_tendsto.pow 2)
        (Filter.Eventually.of_forall hbounds)
    have hsquare : 1 - (tildeBetaCIsing d / beta) ^ 2 ≤
        (sctInfiniteFieldMag d beta h) ^ 2 := by
      unfold sctInfiniteMeanfieldG at hG
      have hb2 : 0 < beta ^ 2 := sq_pos_of_pos hbeta0
      rw [div_pow]
      have hone : 1 - (sctInfiniteFieldMag d beta h) ^ 2 ≤
          (tildeBetaCIsing d) ^ 2 / beta ^ 2 := by
        rw [le_div_iff₀ hb2]
        nlinarith
      linarith
    calc
      Real.sqrt (1 - (tildeBetaCIsing d / beta) ^ 2)
          ≤ Real.sqrt ((sctInfiniteFieldMag d beta h) ^ 2) :=
        Real.sqrt_le_sqrt hsquare
      _ = sctInfiniteFieldMag d beta h := Real.sqrt_sq hm0


theorem sctZeroPlus_meanfield_lower_bound_integrated
    (d : ℕ) (hbdd : BddAbove (tildeBetaCIsingSet d))
    (hcrit : 0 < tildeBetaCIsing d) {beta : ℝ}
    (hbeta : tildeBetaCIsing d ≤ beta) :
    Real.sqrt (1 - (tildeBetaCIsing d / beta) ^ 2) ≤
      sctZeroPlusMag d beta := by
  have hbounds : ∀ k : ℕ,
      Real.sqrt (1 - (tildeBetaCIsing d / beta) ^ 2) ≤
        sctInfiniteFieldMag d beta (sctFieldToZero k) := by
    intro k
    exact sctInfiniteFieldMag_meanfield_lower_bound_integrated d hbdd hcrit
      hbeta (sctFieldToZero_pos k)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    (sctInfiniteFieldMag_tendsto_zeroPlus d beta (hcrit.le.trans hbeta))
    (Filter.Eventually.of_forall hbounds)

end Sharpness
end StatMech
