/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreePairMixingFromTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FK.FreeTailTriviality
import Theorem.StatisticalMechanics.Code.FK.FKTwoBoxDecoupling.Part2
import Theorem.StatisticalMechanics.Code.Foundations.BirkhoffErgodic
import Def.StatisticalMechanics.Code.FK.FreePairMixingFromTail.Part3
open MeasureTheory Set Filter Function
open scoped BigOperators ENNReal Topology


namespace StatMech

namespace FK

open ConfigSpace Lattice

variable {d : ℕ}


theorem freePairGap_nonneg
    (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (T U : Finset (Sym2 (Site d))) (k : ℕ) :
    let mu := (freeInfiniteVolume d hp hp1
      (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
    0 ≤ freePairGap hd mu T U k := by
  dsimp only
  let mu := (freeInfiniteVolume d hp hp1
    (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
  have hti : IsTranslationInvariant (G := Multiplicative (Site d)) mu :=
    bdp_freeIV_isTranslationInvariant hp hp1
  have hfkg := ftb_freeIV_fkg_multiOpen hp hp1 T
    (U.image (fun e => (freeAxisTranslationPower hd k)⁻¹ • e))
  have htrans :
      mu.real (fmu_multiOpen
          (U.image (fun e => (freeAxisTranslationPower hd k)⁻¹ • e))) =
        mu.real (fmu_multiOpen U) := by
    rw [← fmu_shift_multiOpen (freeAxisTranslationPower hd k) U]
    exact fmc_real_preimage_shift hti (freeAxisTranslationPower hd k)
      (fmu_multiOpen_measurable U)
  rw [htrans] at hfkg
  unfold freePairGap
  rw [fmu_shift_multiOpen (freeAxisTranslationPower hd k) U]
  exact sub_nonneg.mpr hfkg

theorem freePairGapAverage_tendsto
    (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (T U : Finset (Sym2 (Site d))) :
    let mu := (freeInfiniteVolume d hp hp1
      (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        freePairGap hd mu T U k) atTop (𝓝 0) := by
  dsimp only
  let mu := (freeInfiniteVolume d hp hp1
    (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
  let c := mu.real (fmu_multiOpen T) * mu.real (fmu_multiOpen U)
  have hcorr := freeInfiniteVolume_pairCorrelationAverage_tendsto
    hd hp hp1 T U
  have hc : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
  have hsub : Tendsto (fun n : ℕ =>
      (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        mu.real (fmu_multiOpen T ∩
          shift (freeAxisTranslationPower hd k) ⁻¹' fmu_multiOpen U) - c)
      atTop (𝓝 0) := by
    simpa only [mu, c, sub_self] using hcorr.sub hc
  apply hsub.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  dsimp only [c, mu]
  simp only [freePairGap, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp


theorem freeInfiniteVolume_pairMixing_all_parameters
    (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    fmu_PairMixing (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) :
        Measure (ConfigSpace (Sym2 (Site d)))) := by
  classical
  let mu := (freeInfiniteVolume d hp hp1
    (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
  intro P delta hdelta
  have htotal : Tendsto (fun n : ℕ =>
      ∑ T ∈ P, ∑ U ∈ P, (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        freePairGap hd mu T U k) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum P (fun T hT =>
      tendsto_finsetSum P (fun U hU =>
        freePairGapAverage_tendsto hd hp hp1 T U))
  have hevent : ∀ᶠ (n : ℕ) in atTop,
      (∑ T ∈ P, ∑ U ∈ P, (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        freePairGap hd mu T U k) < delta :=
    htotal.eventually (eventually_lt_nhds hdelta)
  obtain ⟨n, hn, havg⟩ := ((eventually_ge_atTop 1).and hevent).exists
  have havg' : (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
      ∑ T ∈ P, ∑ U ∈ P, freePairGap hd mu T U k < delta := by
    calc
      (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
          ∑ T ∈ P, ∑ U ∈ P, freePairGap hd mu T U k =
          ∑ T ∈ P, ∑ U ∈ P, (n : ℝ)⁻¹ *
            ∑ k ∈ Finset.range n, freePairGap hd mu T U k := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro T hT
              rw [Finset.sum_comm]
      _ < delta := havg
  have hnR : (0 : ℝ) < n := by positivity
  have hsumlt :
      (∑ k ∈ Finset.range n,
        ∑ T ∈ P, ∑ U ∈ P, freePairGap hd mu T U k) <
      ∑ _k ∈ Finset.range n, delta := by
    calc
      (∑ k ∈ Finset.range n,
          ∑ T ∈ P, ∑ U ∈ P, freePairGap hd mu T U k) =
          (n : ℝ) * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
            ∑ T ∈ P, ∑ U ∈ P, freePairGap hd mu T U k) := by
              field_simp
      _ < (n : ℝ) * delta := mul_lt_mul_of_pos_left havg' hnR
      _ = ∑ _k ∈ Finset.range n, delta := by simp
  obtain ⟨k, hk, hkdelta⟩ := Finset.exists_lt_of_sum_lt hsumlt
  refine ⟨freeAxisTranslationPower hd k, ?_⟩
  intro T hT U hU
  have hinner : freePairGap hd mu T U k ≤
      ∑ U' ∈ P, freePairGap hd mu T U' k := by
    exact Finset.single_le_sum
      (fun U' hU' => freePairGap_nonneg hd hp hp1 T U' k) hU
  have houter : (∑ U' ∈ P, freePairGap hd mu T U' k) ≤
      ∑ T' ∈ P, ∑ U' ∈ P, freePairGap hd mu T' U' k := by
    exact Finset.single_le_sum
      (fun T' hT' => Finset.sum_nonneg fun U' hU' =>
        freePairGap_nonneg hd hp hp1 T' U' k) hT
  have hgaplt : freePairGap hd mu T U k < delta :=
    lt_of_le_of_lt (hinner.trans houter) hkdelta
  change abs (freePairGap hd mu T U k) < delta
  rw [abs_of_nonneg (freePairGap_nonneg hd hp hp1 T U k)]
  exact hgaplt

end FK
end StatMech
