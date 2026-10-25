/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbabilityGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenCoarseBoundaryGeneral.Part2
import Theorem.StatisticalMechanics.Code.Percolation.CanonBurtonKeane
import Theorem.StatisticalMechanics.Code.Walls.bc62coarseclose.Part2
import Def.StatisticalMechanics.Code.FrontierA.AllOpenCoarseProbabilityGeneral
open Finset Set SimpleGraph MeasureTheory Filter Topology
open scoped ENNReal BigOperators


namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace StatMech.Lattice StatMech.Percolation

open StatMech.Walls

variable {d : ℕ}


theorem bgfdFaithfulAllOpenTrifIndicesInBox_count_bound
    (omega : ConfigSpace (Sym2 (Site d))) (L N : ℕ) :
    (bgfdFaithfulAllOpenTrifIndicesInBox omega L N).card ≤
      bgfdFaithfulAllOpenBoundaryCard d L N := by
  exact bgfdFaithfulAllOpenTrifIndicesInBox_count omega L N

lemma bgfd_boxFinsetBK_card_real (d N : ℕ) :
    ((boxFinsetBK d N).card : ℝ) = (2 * (N : ℝ) + 1) ^ d := by
  unfold boxFinsetBK
  rw [← boxSV_boxF_eq_toFinset, boxSV_card_boxF]
  push_cast
  ring


theorem bgfdFaithfulAllOpen_boundary_volume_ratio_le
    (d L N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N) :
    (bgfdFaithfulAllOpenBoundaryCard d L N : ℝ) /
        ((boxFinsetBK d N).card : ℝ) ≤
      (2 * (d : ℝ) * ((3 * L + 2 : ℕ) : ℝ) ^ d) / N := by
  let R : ℕ := (2 * L + 1) * N + L + 1
  have hR : 1 ≤ R := by simp [R]
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hVR : ((boxFinsetBK d R).card : ℝ) =
      (2 * (R : ℝ) + 1) ^ d := bgfd_boxFinsetBK_card_real d R
  have hVN : ((boxFinsetBK d N).card : ℝ) =
      (2 * (N : ℝ) + 1) ^ d := bgfd_boxFinsetBK_card_real d N
  have hVRpos : (0 : ℝ) < ((boxFinsetBK d R).card : ℝ) := by
    rw [hVR]
    positivity
  have hVNpos : (0 : ℝ) < ((boxFinsetBK d N).card : ℝ) := by
    rw [hVN]
    positivity
  have hsurface : (boxSV_boundaryCard d R : ℝ) ≤
      (2 * (d : ℝ) / R) * ((boxFinsetBK d R).card : ℝ) := by
    apply (div_le_iff₀ hVRpos).mp
    simpa using bkc_boundary_vol_ratio_le d R hd hR
  have hbase : (2 * (R : ℝ) + 1) ≤
      ((3 * L + 2 : ℕ) : ℝ) * (2 * (N : ℝ) + 1) := by
    dsimp [R]
    push_cast
    nlinarith [show (0 : ℝ) ≤ L by positivity,
      show (1 : ℝ) ≤ N by exact_mod_cast hN]
  have hvolume : ((boxFinsetBK d R).card : ℝ) ≤
      ((3 * L + 2 : ℕ) : ℝ) ^ d *
        ((boxFinsetBK d N).card : ℝ) := by
    rw [hVR, hVN, ← mul_pow]
    exact (pow_le_pow_left₀ (by positivity) hbase) d
  have hNR : (N : ℝ) ≤ R := by
    have hfac : 1 ≤ 2 * L + 1 := by omega
    have hmul : 1 * N ≤ (2 * L + 1) * N :=
      Nat.mul_le_mul_right N hfac
    exact_mod_cast (show N ≤ R by dsimp [R]; omega)
  have hcoef : 2 * (d : ℝ) / R ≤ 2 * (d : ℝ) / N := by
    rw [div_le_div_iff₀ hRpos hNpos]
    nlinarith [show (0 : ℝ) ≤ d by positivity]
  have hfinal : (boxSV_boundaryCard d R : ℝ) ≤
      ((2 * (d : ℝ) * ((3 * L + 2 : ℕ) : ℝ) ^ d) / N) *
        ((boxFinsetBK d N).card : ℝ) := by
    calc
      (boxSV_boundaryCard d R : ℝ) ≤
          (2 * (d : ℝ) / R) *
            ((boxFinsetBK d R).card : ℝ) := hsurface
      _ ≤ (2 * (d : ℝ) / R) *
            (((3 * L + 2 : ℕ) : ℝ) ^ d *
              ((boxFinsetBK d N).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hvolume (by positivity)
      _ ≤ (2 * (d : ℝ) / N) *
            (((3 * L + 2 : ℕ) : ℝ) ^ d *
              ((boxFinsetBK d N).card : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = (2 * (d : ℝ) * ((3 * L + 2 : ℕ) : ℝ) ^ d / N) *
            ((boxFinsetBK d N).card : ℝ) := by ring
  rw [div_le_iff₀ hVNpos]
  simpa [bgfdFaithfulAllOpenBoundaryCard, R] using hfinal

theorem bgfdFaithfulAllOpen_boundary_volume_tendsto
    (d L : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun N => (bgfdFaithfulAllOpenBoundaryCard d L N : ℝ) /
      ((boxFinsetBK d N).card : ℝ)) atTop (nhds 0) := by
  have htop : Tendsto
      (fun N : ℕ =>
        (2 * (d : ℝ) * ((3 * L + 2 : ℕ) : ℝ) ^ d) / N)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds
      (x := 2 * (d : ℝ) * ((3 * L + 2 : ℕ) : ℝ) ^ d)).div_atTop
        tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall (fun N => by positivity)) ?_ htop
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact bgfdFaithfulAllOpen_boundary_volume_ratio_le d L N hd hN


theorem bgfdFaithfulAllOpenTrifAt_prob_eq_zero
    (mu : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure mu]
    (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
    (L : ℕ) :
    mu {omega | BgfdFaithfulAllOpenTrifAt omega L 0} = 0 := by
  classical
  let p : ℝ≥0∞ := mu {omega | BgfdFaithfulAllOpenTrifAt omega L 0}
  have hkey : ∀ N,
      ((boxFinsetBK d N).card : ℝ≥0∞) * p ≤
        (bgfdFaithfulAllOpenBoundaryCard d L N : ℝ≥0∞) := by
    intro N
    have hexp := expected_bgfdFaithfulAllOpenTrifIndicesInBox mu hinv L N
    rw [nsmul_eq_mul] at hexp
    have hle : ∫⁻ omega,
        ((bgfdFaithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) ∂mu ≤
        (bgfdFaithfulAllOpenBoundaryCard d L N : ℝ≥0∞) := by
      calc
        ∫⁻ omega,
            ((bgfdFaithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) ∂mu ≤
            ∫⁻ _omega,
              (bgfdFaithfulAllOpenBoundaryCard d L N : ℝ≥0∞) ∂mu := by
          apply lintegral_mono
          intro omega
          change ((bgfdFaithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) ≤
            (bgfdFaithfulAllOpenBoundaryCard d L N : ℝ≥0∞)
          exact_mod_cast
            bgfdFaithfulAllOpenTrifIndicesInBox_count_bound omega L N
        _ = (bgfdFaithfulAllOpenBoundaryCard d L N : ℝ≥0∞) := by
          rw [lintegral_const]
          simp
    rwa [hexp] at hle
  have hpfin : p ≠ ⊤ := measure_ne_top mu _
  let pr : ℝ := p.toReal
  have hprnn : 0 ≤ pr := ENNReal.toReal_nonneg
  have hkeyr : ∀ N,
      ((boxFinsetBK d N).card : ℝ) * pr ≤
        (bgfdFaithfulAllOpenBoundaryCard d L N : ℝ) := by
    intro N
    have h := hkey N
    have h' : (((boxFinsetBK d N).card : ℝ≥0∞) * p).toReal ≤
        (bgfdFaithfulAllOpenBoundaryCard d L N : ℝ≥0∞).toReal :=
      ENNReal.toReal_mono (by simp) h
    rw [ENNReal.toReal_mul] at h'
    simpa [ENNReal.toReal_natCast, pr] using h'
  have hvolr : ∀ N, (0 : ℝ) < ((boxFinsetBK d N).card : ℝ) := by
    intro N
    exact_mod_cast bkc_boxFinsetBK_card_pos d N
  have hle : ∀ N, pr ≤
      (bgfdFaithfulAllOpenBoundaryCard d L N : ℝ) /
        ((boxFinsetBK d N).card : ℝ) := by
    intro N
    rw [le_div_iff₀ (hvolr N)]
    linarith [hkeyr N]
  have hpr0 : pr ≤ 0 := le_of_tendsto_of_tendsto'
    tendsto_const_nhds
      (bgfdFaithfulAllOpen_boundary_volume_tendsto d L hd) hle
  have hpreq : pr = 0 := le_antisymm hpr0 hprnn
  have hptoreal : p.toReal = 0 := hpreq
  have hpzero : p = 0 :=
    (ENNReal.toReal_eq_zero_iff p).mp hptoreal |>.resolve_right hpfin
  exact hpzero

end StatMech.FrontierA
