/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxCritical.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.PottsCriticalCorrespondence.Part2
import Def.StatisticalMechanics.Code.OSSS.WiredBoxCriticalGeneral.Part3
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace WiredBoxCriticalGeneral

open Filter

open WiredBoxSharpness WiredBoxCritical

open WiredBoxLocalized

theorem fkCriticalBetaQ_pos
    (d : Nat) (q : Real) (hd : 2 <= d) (hq : 1 <= q) :
    0 < fkCriticalBetaQ d q := by
  have hpc0 := FK.fkPc_pos_of_two_le hd hq
  have hpc1 := FK.fkPc_lt_one_of_two_le hd hq
  unfold fkCriticalBetaQ
  exact neg_pos.mpr (Real.log_neg (sub_pos.mpr hpc1) (by linarith))

theorem fkCriticalBetaQ_param
    (d : Nat) (q : Real) (hd : 2 <= d) (hq : 1 <= q) :
    1 - Real.exp (-fkCriticalBetaQ d q) = FK.fkPc d q := by
  have hpc1 := FK.fkPc_lt_one_of_two_le hd hq
  unfold fkCriticalBetaQ
  rw [neg_neg, Real.exp_log (sub_pos.mpr hpc1)]
  ring

theorem betaToP_lt_fkPc_of_lt_fkCriticalBetaQ
    (d : Nat) (q : Real) (hd : 2 <= d) (hq : 1 <= q) {beta : Real}
    (hbeta : beta < fkCriticalBetaQ d q) :
    1 - Real.exp (-beta) < FK.fkPc d q := by
  rw [← fkCriticalBetaQ_param d q hd hq]
  have hexp : Real.exp (-fkCriticalBetaQ d q) < Real.exp (-beta) :=
    Real.exp_lt_exp.mpr (by linarith)
  linarith

theorem fkPc_lt_betaToP_of_fkCriticalBetaQ_lt
    (d : Nat) (q : Real) (hd : 2 <= d) (hq : 1 <= q) {beta : Real}
    (hbeta : fkCriticalBetaQ d q < beta) :
    FK.fkPc d q < 1 - Real.exp (-beta) := by
  rw [← fkCriticalBetaQ_param d q hd hq]
  have hexp : Real.exp (-beta) < Real.exp (-fkCriticalBetaQ d q) :=
    Real.exp_lt_exp.mpr (by linarith)
  linarith


theorem wiredBeta1Q_eq_fkCriticalBetaQ_of_ge
    (d : Nat) (q beta0 : Real) (hd : 2 <= d) (hq : 1 <= q)
    (hbeta0 : fkCriticalBetaQ d q <= beta0) :
    wiredBeta1Q d q beta0 = fkCriticalBetaQ d q := by
  let betaC := fkCriticalBetaQ d q
  let Sgf : Real -> Nat -> Real := fun b n =>
    IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n b
  have hbetaCpos : 0 < betaC := fkCriticalBetaQ_pos d q hd hq
  have hbeta0pos : 0 < beta0 := hbetaCpos.trans_le hbeta0
  have hbdd : BddBelow (BetaThresholdBound.thresholdSet Sgf) := by
    simpa [Sgf] using wiredThresholdSet_bddBelow d q beta0
  have hle : wiredBeta1Q d q beta0 <= betaC := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro beta hbetaCbeta
    have hbetapos : 0 < beta := hbetaCpos.trans hbetaCbeta
    have hp : 0 < 1 - Real.exp (-beta) := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
      linarith
    have hp1 : 1 - Real.exp (-beta) < 1 := by
      linarith [Real.exp_pos (-beta)]
    have htheta : 0 < FK.fkTheta d hp hp1
        (zero_lt_one.trans_le hq) (q := q) :=
      FK.frp_fkTheta_pos_of_gt_fkPc d hp hp1 (zero_lt_one.trans_le hq)
        (fkPc_lt_betaToP_of_fkCriticalBetaQ_lt d q hd hq hbetaCbeta)
    have hmem := wiredThresholdSet_mem_of_fkTheta_pos
      d q beta0 beta hq hbetapos htheta
    unfold wiredBeta1Q BetaThresholdBound.beta1
    exact csInf_le hbdd (by simpa [Sgf] using hmem)
  have hge : betaC <= wiredBeta1Q d q beta0 := by
    by_contra hnot
    have hlt : wiredBeta1Q d q beta0 < betaC := lt_of_not_ge hnot
    let beta := (wiredBeta1Q d q beta0 + betaC) / 2
    have hcrit : wiredBeta1Q d q beta0 < beta := by dsimp [beta]; linarith
    have hbetaC : beta < betaC := by dsimp [beta]; linarith
    have hbetapos : 0 < beta :=
      lt_of_le_of_lt (wiredBeta1Q_nonneg d q beta0 hd hq) hcrit
    have hmean := betaFKThetaQ_meanField_lower
      d q beta0 beta hd hq hcrit (hbetaC.le.trans hbeta0)
    have hthetaPos : 0 < betaFKThetaQ d q hq beta := by
      have hc := wiredSharpConstant_pos d beta0
      have hgap : 0 < beta - wiredBeta1Q d q beta0 := sub_pos.mpr hcrit
      nlinarith
    have hp : 0 < 1 - Real.exp (-beta) := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
      linarith
    have hp1 : 1 - Real.exp (-beta) < 1 := by
      linarith [Real.exp_pos (-beta)]
    have hzero : FK.fkTheta d hp hp1
        (zero_lt_one.trans_le hq) (q := q) = 0 :=
      FK.fkgq_fkTheta_eq_zero_of_lt_pc hp hp1 hq
        (betaToP_lt_fkPc_of_lt_fkCriticalBetaQ d q hd hq hbetaC)
    rw [betaFKThetaQ_eq d q hq beta hbetapos, hzero] at hthetaPos
    exact (lt_irrefl 0 hthetaPos)
  exact le_antisymm hle hge


theorem wiredOuterInner_exponential_decay_below_fkCriticalBetaQ
    (d : Nat) (q beta : Real) (hd : 2 <= d) (hq : 1 <= q)
    (hbeta : 0 < beta) (hsub : beta < fkCriticalBetaQ d q) :
    ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 <= n ->
      wiredOuterInnerTheta d q beta n <=
        Real.exp (-((n : Real) / Q *
          ((fkCriticalBetaQ d q - beta) / 4))) := by
  let betaC := fkCriticalBetaQ d q
  let betaMid := (beta + betaC) / 2
  let delta := (betaC - beta) / 4
  have hdelta : 0 < delta := by dsimp [delta, betaC]; linarith
  have hleft : betaMid - 2 * delta = beta := by
    dsimp [betaMid, delta]
    ring
  have hmidLe : betaMid <= betaC := by dsimp [betaMid]; linarith
  have hthreshold : wiredBeta1Q d q betaC = betaC :=
    wiredBeta1Q_eq_fkCriticalBetaQ_of_ge d q betaC hd hq le_rfl
  have hmidThreshold : betaMid < wiredBeta1Q d q betaC := by
    rw [hthreshold]
    dsimp [betaMid]
    linarith
  obtain ⟨Q, hQ, hdecay⟩ :=
    wiredOuterInner_subcritical_decay_of_threshold
      d q delta betaMid betaC hq hmidLe hdelta
      (by rw [hleft]; exact hbeta)
      (by simpa [wiredBeta1Q] using hmidThreshold)
  refine ⟨Q, hQ, ?_⟩
  intro n hn
  simpa [hleft, delta, betaC, mul_assoc] using hdecay n hn


theorem betaFKThetaQ_meanField_above_fkCriticalBetaQ
    (d : Nat) (q beta : Real) (hd : 2 <= d) (hq : 1 <= q)
    (hsuper : fkCriticalBetaQ d q < beta) :
    wiredSharpConstant d beta * (beta - fkCriticalBetaQ d q) <=
      betaFKThetaQ d q hq beta := by
  have hthreshold : wiredBeta1Q d q beta = fkCriticalBetaQ d q :=
    wiredBeta1Q_eq_fkCriticalBetaQ_of_ge d q beta hd hq hsuper.le
  have hcrit : wiredBeta1Q d q beta < beta := by rwa [hthreshold]
  simpa [hthreshold] using
    betaFKThetaQ_meanField_lower d q beta beta hd hq hcrit le_rfl


theorem fkSharpness_homogeneous
    (d : Nat) (q : Real) (hd : 2 <= d) (hq : 1 <= q) :
    (forall beta, fkCriticalBetaQ d q <= beta ->
      wiredSharpConstant d beta * (beta - fkCriticalBetaQ d q) <=
        betaFKThetaQ d q hq beta) ∧
    (forall beta, 0 < beta -> beta < fkCriticalBetaQ d q ->
      ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 <= n ->
        wiredOuterInnerTheta d q beta n <=
          Real.exp (-((n : Real) / Q *
            ((fkCriticalBetaQ d q - beta) / 4)))) := by
  constructor
  · intro beta hbeta
    rcases hbeta.eq_or_lt with rfl | hsuper
    · simpa using betaFKThetaQ_nonneg d q hq (fkCriticalBetaQ d q)
    · exact betaFKThetaQ_meanField_above_fkCriticalBetaQ
        d q beta hd hq hsuper
  · intro beta hbeta hsub
    exact wiredOuterInner_exponential_decay_below_fkCriticalBetaQ
      d q beta hd hq hbeta hsub

end WiredBoxCriticalGeneral
end OSSS
end StatMech
