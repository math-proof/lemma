/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/PottsCriticalCorrespondence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.IsingFK.BetacPc.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperAllDimensions
import Theorem.StatisticalMechanics.Code.FK.FreePercolationFull
import Def.StatisticalMechanics.Code.IsingFK.PottsCriticalCorrespondence
open Real Set


namespace StatMech

namespace IsingFK

theorem pottsFKMagnetization_nonneg (d : ℕ) (q : ℝ) (hq : 1 < q) (beta : ℝ) :
    0 ≤ pottsFKMagnetization d q hq beta := by
  rw [pottsFKMagnetization]
  split_ifs with hbeta
  · exact FK.fkTheta_nonneg d _ _ _
  · exact le_rfl


theorem pottsFKMagnetization_eq_zero_of_lt_critical
    {d : ℕ} {q beta : ℝ} (hq : 1 < q) (hpc1 : FK.fkPc d q < 1)
    (hbeta : 0 < beta)
    (hbelow : beta < pToBeta q (FK.fkPc d q)) :
    pottsFKMagnetization d q hq beta = 0 := by
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q ≠ 1 := by linarith
  have hp : 0 < betaToP q beta := by
    rw [← betaToP_zero q]
    exact (strictMono_betaToP q hq) hbeta
  have hp1 : betaToP q beta < 1 := (betaToP_mem q beta hq hbeta.le).2
  have hparam : betaToP q beta < FK.fkPc d q := by
    have h := (strictMono_betaToP q hq) hbelow
    rwa [betaToP_pToBeta q (FK.fkPc d q) hq0 hq1 hpc1] at h
  rw [pottsFKMagnetization, dif_pos hbeta]
  exact FK.fkgq_fkTheta_eq_zero_of_lt_pc hp hp1 hq.le hparam


theorem pottsFKMagnetization_pos_of_critical_lt
    {d : ℕ} {q beta : ℝ} (hq : 1 < q)
    (hpc0 : 0 ≤ FK.fkPc d q) (hpc1 : FK.fkPc d q < 1)
    (habove : pToBeta q (FK.fkPc d q) < beta) :
    0 < pottsFKMagnetization d q hq beta := by
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q ≠ 1 := by linarith
  have hthreshold_nonneg : 0 ≤ pToBeta q (FK.fkPc d q) :=
    pToBeta_mem q (FK.fkPc d q) hq ⟨hpc0, hpc1⟩
  have hbeta : 0 < beta := lt_of_le_of_lt hthreshold_nonneg habove
  have hp : 0 < betaToP q beta := by
    rw [← betaToP_zero q]
    exact (strictMono_betaToP q hq) hbeta
  have hp1 : betaToP q beta < 1 := (betaToP_mem q beta hq hbeta.le).2
  have hparam : FK.fkPc d q < betaToP q beta := by
    have h := (strictMono_betaToP q hq) habove
    rwa [betaToP_pToBeta q (FK.fkPc d q) hq0 hq1 hpc1] at h
  rw [pottsFKMagnetization, dif_pos hbeta]
  exact FK.frp_fkTheta_pos_of_gt_fkPc d hp hp1 (zero_lt_one.trans hq) hparam


theorem pottsFK_betaC_eq (d : ℕ) {q : ℝ} (hd : 2 ≤ d) (hq : 1 < q) :
    betaC (pottsFKMagnetization d q hq) =
      -((q - 1) / q) * Real.log (1 - FK.fkPc d q) := by
  have hpc0 : 0 < FK.fkPc d q := FK.fkPc_pos_of_two_le hd hq.le
  have hpc1 : FK.fkPc d q < 1 := FK.fkPc_lt_one_of_two_le hd hq.le
  have ht : 0 < pToBeta q (FK.fkPc d q) := by
    rw [← pToBeta_zero q]
    exact (strictMonoOn_pToBeta q hq) (Set.mem_Iio.mpr (by norm_num))
      (Set.mem_Iio.mpr hpc1) hpc0
  exact betaC_eq_of_strict_transition
    (pottsFKMagnetization d q hq) (pToBeta q (FK.fkPc d q))
    ht
    (fun beta hbeta hbelow =>
      pottsFKMagnetization_eq_zero_of_lt_critical hq hpc1 hbeta hbelow)
    (fun beta habove =>
      pottsFKMagnetization_pos_of_critical_lt hq hpc0.le hpc1 habove)

end IsingFK
end StatMech
