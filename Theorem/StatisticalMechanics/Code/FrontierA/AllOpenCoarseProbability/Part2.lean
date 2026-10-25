/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenCoarseBoundary.Part3
import Theorem.StatisticalMechanics.Code.Walls.bdcdetcount.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc62coarseclose.Part2
import Def.StatisticalMechanics.Code.FrontierA.AllOpenCoarseProbability
open Finset Set SimpleGraph MeasureTheory Filter Topology
open scoped ENNReal BigOperators


namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace StatMech.Lattice StatMech.Percolation

open StatMech.Walls


theorem faithfulAllOpenTrifIndicesInBox_count_bound
    (omega : ConfigSpace (Sym2 (Site 2))) (L N : ℕ) :
    (faithfulAllOpenTrifIndicesInBox omega L N).card ≤
      faithfulAllOpenBoundaryCard L N := by
  exact faithfulAllOpenTrifIndicesInBox_count omega L N

lemma boxSV_boundaryCard_two (r : ℕ) (hr : 1 ≤ r) :
    (boxSV_boundaryCard 2 r : ℝ) = 8 * r := by
  rw [boxSV_boundary_card 2 r hr]
  have hle : (2 * r - 1) ^ 2 ≤ (2 * r + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  rw [Nat.cast_sub hle]
  have hsub : 1 ≤ 2 * r := by omega
  push_cast [Nat.cast_sub hsub]
  ring

lemma boxFinsetBK_card_two (N : ℕ) :
    ((boxFinsetBK 2 N).card : ℝ) = (2 * (N : ℝ) + 1) ^ 2 := by
  unfold boxFinsetBK
  rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF]
  push_cast
  ring

theorem faithfulAllOpen_boundary_volume_ratio_le
    (L N : ℕ) (hN : 1 ≤ N) :
    (faithfulAllOpenBoundaryCard L N : ℝ) /
        ((boxFinsetBK 2 N).card : ℝ) ≤
      (8 * (3 * L + 2) : ℝ) / N := by
  rw [faithfulAllOpenBoundaryCard,
    boxSV_boundaryCard_two _ (by omega), boxFinsetBK_card_two]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (2 * N + 1) ^ 2)
    (by exact_mod_cast hN : (0 : ℝ) < N)]
  push_cast
  nlinarith [show (0 : ℝ) ≤ L by positivity,
    show (1 : ℝ) ≤ N by exact_mod_cast hN]

theorem faithfulAllOpen_boundary_volume_tendsto (L : ℕ) :
    Tendsto (fun N => (faithfulAllOpenBoundaryCard L N : ℝ) /
      ((boxFinsetBK 2 N).card : ℝ)) atTop (𝓝 0) := by
  have htop : Tendsto (fun N : ℕ => (8 * (3 * L + 2) : ℝ) / N)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds
      (x := (8 * (3 * L + 2) : ℝ))).div_atTop
        tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall (fun N => by positivity)) ?_ htop
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact faithfulAllOpen_boundary_volume_ratio_le L N hN


theorem faithfulAllOpenTrifAt_prob_eq_zero
    (mu : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure mu]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) mu)
    (L : ℕ) :
    mu {omega | FaithfulAllOpenTrifAt omega L 0} = 0 := by
  classical
  let p : ℝ≥0∞ := mu {omega | FaithfulAllOpenTrifAt omega L 0}
  have hkey : ∀ N,
      ((boxFinsetBK 2 N).card : ℝ≥0∞) * p ≤
        (faithfulAllOpenBoundaryCard L N : ℝ≥0∞) := by
    intro N
    have hexp := expected_faithfulAllOpenTrifIndicesInBox mu hinv L N
    rw [nsmul_eq_mul] at hexp
    have hle : ∫⁻ omega,
        ((faithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) ∂mu ≤
        (faithfulAllOpenBoundaryCard L N : ℝ≥0∞) := by
      calc
        ∫⁻ omega,
            ((faithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) ∂mu ≤
            ∫⁻ _omega, (faithfulAllOpenBoundaryCard L N : ℝ≥0∞) ∂mu := by
          apply lintegral_mono
          intro omega
          change ((faithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) ≤
            (faithfulAllOpenBoundaryCard L N : ℝ≥0∞)
          exact_mod_cast
            faithfulAllOpenTrifIndicesInBox_count_bound omega L N
        _ = (faithfulAllOpenBoundaryCard L N : ℝ≥0∞) := by
          rw [lintegral_const]
          simp
    rwa [hexp] at hle
  have hpfin : p ≠ ⊤ := measure_ne_top mu _
  let pr : ℝ := p.toReal
  have hprnn : 0 ≤ pr := ENNReal.toReal_nonneg
  have hkeyr : ∀ N,
      ((boxFinsetBK 2 N).card : ℝ) * pr ≤
        (faithfulAllOpenBoundaryCard L N : ℝ) := by
    intro N
    have h := hkey N
    have h' : (((boxFinsetBK 2 N).card : ℝ≥0∞) * p).toReal ≤
        (faithfulAllOpenBoundaryCard L N : ℝ≥0∞).toReal :=
      ENNReal.toReal_mono (by simp) h
    rw [ENNReal.toReal_mul] at h'
    simpa [ENNReal.toReal_natCast, pr] using h'
  have hvolr : ∀ N, (0 : ℝ) < ((boxFinsetBK 2 N).card : ℝ) := by
    intro N
    exact_mod_cast bkc_boxFinsetBK_card_pos 2 N
  have hle : ∀ N, pr ≤ (faithfulAllOpenBoundaryCard L N : ℝ) /
      ((boxFinsetBK 2 N).card : ℝ) := by
    intro N
    rw [le_div_iff₀ (hvolr N)]
    linarith [hkeyr N]
  have hpr0 : pr ≤ 0 := le_of_tendsto_of_tendsto'
    tendsto_const_nhds (faithfulAllOpen_boundary_volume_tendsto L) hle
  have hpreq : pr = 0 := le_antisymm hpr0 hprnn
  have hptoreal : p.toReal = 0 := hpreq
  have hpzero : p = 0 :=
    (ENNReal.toReal_eq_zero_iff p).mp hptoreal |>.resolve_right hpfin
  exact hpzero

end StatMech.FrontierA
