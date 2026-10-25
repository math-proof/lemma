/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxSharpness
import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
import Theorem.StatisticalMechanics.Code.FK.FreePercolationFull
import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperAllDimensions
import Def.StatisticalMechanics.Code.OSSS.WiredBoxCritical.Part3
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace WiredBoxCritical

open Filter

open WiredBoxSharpness

open Lattice FK

open WiredBoxLocalized WiredBoxOffCentre

open MeasureTheory


theorem fkCriticalBeta_pos (d : Nat) (hd : 2 <= d) :
    0 < fkCriticalBeta d := by
  have hpc0 := FK.fkPc_pos_of_two_le hd (by norm_num : (1 : Real) <= 2)
  have hpc1 := FK.fkPc_two_lt_one_of_two_le hd
  unfold fkCriticalBeta
  exact neg_pos.mpr (Real.log_neg (sub_pos.mpr hpc1) (by linarith))

theorem fkCriticalBeta_param (d : Nat) (hd : 2 <= d) :
    1 - Real.exp (-fkCriticalBeta d) = FK.fkPc d 2 := by
  have hpc1 := FK.fkPc_two_lt_one_of_two_le hd
  unfold fkCriticalBeta
  rw [neg_neg, Real.exp_log (sub_pos.mpr hpc1)]
  ring

theorem betaToP_lt_fkPc_of_lt_fkCriticalBeta
    (d : Nat) (hd : 2 <= d) {beta : Real}
    (hbeta : beta < fkCriticalBeta d) :
    1 - Real.exp (-beta) < FK.fkPc d 2 := by
  rw [← fkCriticalBeta_param d hd]
  have hexp : Real.exp (-fkCriticalBeta d) < Real.exp (-beta) :=
    Real.exp_lt_exp.mpr (by linarith)
  linarith

theorem fkPc_lt_betaToP_of_fkCriticalBeta_lt
    (d : Nat) (hd : 2 <= d) {beta : Real}
    (hbeta : fkCriticalBeta d < beta) :
    FK.fkPc d 2 < 1 - Real.exp (-beta) := by
  rw [← fkCriticalBeta_param d hd]
  have hexp : Real.exp (-beta) < Real.exp (-fkCriticalBeta d) :=
    Real.exp_lt_exp.mpr (by linarith)
  linarith


theorem wiredBeta1_eq_fkCriticalBeta_q2_of_ge
    (d : Nat) (beta0 : Real) (hd : 2 <= d)
    (hbeta0 : fkCriticalBeta d <= beta0) :
    wiredBeta1 d beta0 = fkCriticalBeta d := by
  let betaC := fkCriticalBeta d
  let Sgf : Real -> Nat -> Real := fun b n =>
    IntegrationSubcritical.Sig
      (wiredThresholdTheta d 2 beta0) n b
  have hbetaCpos : 0 < betaC := fkCriticalBeta_pos d hd
  have hbeta0pos : 0 < beta0 := hbetaCpos.trans_le hbeta0
  have hne : (BetaThresholdBound.thresholdSet Sgf).Nonempty := by
    simpa [Sgf] using wiredThresholdSet_nonempty_q2 d beta0 hd
  have hbdd : BddBelow (BetaThresholdBound.thresholdSet Sgf) := by
    simpa [Sgf] using wiredThresholdSet_bddBelow d 2 beta0
  have hle : wiredBeta1 d beta0 <= betaC := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro beta hbetaCbeta
    have hbetapos : 0 < beta := hbetaCpos.trans hbetaCbeta
    have hp : 0 < 1 - Real.exp (-beta) := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
      linarith
    have hp1 : 1 - Real.exp (-beta) < 1 := by
      linarith [Real.exp_pos (-beta)]
    have htheta : 0 < FK.fkTheta d hp hp1
        (by norm_num : (0 : Real) < 2) (q := 2) :=
      FK.frp_fkTheta_pos_of_gt_fkPc d hp hp1 (by norm_num)
        (fkPc_lt_betaToP_of_fkCriticalBeta_lt d hd hbetaCbeta)
    have hmem := wiredThresholdSet_mem_of_fkTheta_pos_q2
      d beta0 beta hbetapos htheta
    unfold wiredBeta1 BetaThresholdBound.beta1
    exact csInf_le hbdd (by simpa [Sgf] using hmem)
  have hge : betaC <= wiredBeta1 d beta0 := by
    by_contra hnot
    have hlt : wiredBeta1 d beta0 < betaC := lt_of_not_ge hnot
    let beta := (wiredBeta1 d beta0 + betaC) / 2
    have hcrit : wiredBeta1 d beta0 < beta := by dsimp [beta]; linarith
    have hbetaC : beta < betaC := by dsimp [beta]; linarith
    have hbetapos : 0 < beta :=
      lt_of_le_of_lt (wiredBeta1_nonneg_q2 d beta0 hd) hcrit
    have hmean := betaFKTheta_meanField_lower_q2
      d beta0 beta hd hcrit (hbetaC.le.trans hbeta0)
    have hthetaPos : 0 < betaFKTheta d beta := by
      have hc := wiredSharpConstant_pos d beta0
      have hgap : 0 < beta - wiredBeta1 d beta0 := sub_pos.mpr hcrit
      nlinarith
    have hp : 0 < 1 - Real.exp (-beta) := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
      linarith
    have hp1 : 1 - Real.exp (-beta) < 1 := by
      linarith [Real.exp_pos (-beta)]
    have hzero : FK.fkTheta d hp hp1
        (by norm_num : (0 : Real) < 2) (q := 2) = 0 :=
      FK.tzp_fkTheta_eq_zero_of_lt_pc hp hp1
        (betaToP_lt_fkPc_of_lt_fkCriticalBeta d hd hbetaC)
    rw [betaFKTheta_eq d beta hbetapos, hzero] at hthetaPos
    exact (lt_irrefl 0 hthetaPos)
  exact le_antisymm hle hge

theorem wiredBeta1_eq_fkCriticalBeta_q2 (d : Nat) (hd : 2 <= d) :
    wiredBeta1 d (fkCriticalBeta d) = fkCriticalBeta d :=
  wiredBeta1_eq_fkCriticalBeta_q2_of_ge d (fkCriticalBeta d) hd le_rfl


theorem wiredOuterInner_exponential_decay_below_fkCriticalBeta_q2
    (d : Nat) (beta : Real) (hd : 2 <= d)
    (hbeta : 0 < beta) (hsub : beta < fkCriticalBeta d) :
    ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 <= n ->
      wiredOuterInnerTheta d 2 beta n <=
        Real.exp (-((n : Real) / Q *
          ((fkCriticalBeta d - beta) / 4))) := by
  let betaMid := (beta + fkCriticalBeta d) / 2
  let delta := (fkCriticalBeta d - beta) / 4
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hleft : betaMid - 2 * delta = beta := by
    dsimp [betaMid, delta]
    ring
  have hmidPos : 0 < betaMid := by dsimp [betaMid]; linarith
  have hmidLe : betaMid <= fkCriticalBeta d := by dsimp [betaMid]; linarith
  have hmidThreshold : betaMid < wiredBeta1 d (fkCriticalBeta d) := by
    rw [wiredBeta1_eq_fkCriticalBeta_q2 d hd]
    dsimp [betaMid]
    linarith
  obtain ⟨Q, hQ, hdecay⟩ :=
    wiredOuterInner_subcritical_decay_of_threshold
      d 2 delta betaMid (fkCriticalBeta d) (by norm_num) hmidLe hdelta
      (by rw [hleft]; exact hbeta) (by simpa [wiredBeta1] using hmidThreshold)
  refine ⟨Q, hQ, ?_⟩
  intro n hn
  simpa [hleft, delta, mul_assoc] using hdecay n hn


theorem betaFKTheta_meanField_above_fkCriticalBeta_q2
    (d : Nat) (beta : Real) (hd : 2 <= d)
    (hsuper : fkCriticalBeta d < beta) :
    wiredSharpConstant d beta * (beta - fkCriticalBeta d) <=
      betaFKTheta d beta := by
  have hthreshold : wiredBeta1 d beta = fkCriticalBeta d :=
    wiredBeta1_eq_fkCriticalBeta_q2_of_ge d beta hd hsuper.le
  have hcrit : wiredBeta1 d beta < beta := by rwa [hthreshold]
  simpa [hthreshold] using
    betaFKTheta_meanField_lower_q2 d beta beta hd hcrit le_rfl

end WiredBoxCritical
end OSSS
end StatMech
