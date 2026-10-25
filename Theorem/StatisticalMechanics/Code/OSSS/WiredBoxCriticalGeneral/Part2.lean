/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxCritical.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.PottsCriticalCorrespondence.Part2
import Def.StatisticalMechanics.Code.OSSS.WiredBoxCriticalGeneral.Part2
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace WiredBoxCriticalGeneral

open Filter

open WiredBoxSharpness WiredBoxCritical

open WiredBoxLocalized

theorem betaCriticalQ_eq_fkBetaCriticalQ
    (d : Nat) (q : Real) (hd : 2 <= d) (hq : 1 <= q) :
    sSup (BetaCMatch.bcm_subcriticalSet (betaFKThetaQ d q hq)) =
      fkBetaCriticalQ d q := by
  let pc := FK.fkPc d q
  let betaC := fkBetaCriticalQ d q
  have hpc0 : 0 < pc := FK.fkPc_pos_of_two_le hd hq
  have hpc1 : pc < 1 := FK.fkPc_lt_one_of_two_le hd hq
  have hremain : 0 < 1 - pc := by linarith
  have hremain1 : 1 - pc < 1 := by linarith
  have hbetaC : 0 < betaC := by
    dsimp [betaC, fkBetaCriticalQ]
    exact neg_pos.mpr (Real.log_neg hremain hremain1)
  have hparam : 1 - Real.exp (-betaC) = pc := by
    dsimp [betaC, fkBetaCriticalQ]
    rw [neg_neg, Real.exp_log hremain]
    ring
  apply BetaCMatch.bcm_betaC_eq_threshold (betaFKThetaQ d q hq) betaC
  · intro beta hbelow
    by_cases hbeta : 0 < beta
    · rw [betaFKThetaQ_eq d q hq beta hbeta]
      have hp : 0 < 1 - Real.exp (-beta) := by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith
      have hp1 : 1 - Real.exp (-beta) < 1 := by
        linarith [Real.exp_pos (-beta)]
      have hexp : Real.exp (-betaC) < Real.exp (-beta) :=
        Real.exp_lt_exp.mpr (by linarith)
      apply FK.fkgq_fkTheta_eq_zero_of_lt_pc hp hp1 hq
      have hlt : 1 - Real.exp (-beta) < pc := by
        rw [← hparam]
        linarith
      simpa [pc] using hlt
    · simp [betaFKThetaQ, hbeta]
  · intro beta habove
    have hbeta : 0 < beta := hbetaC.trans habove
    rw [betaFKThetaQ_eq d q hq beta hbeta]
    have hp : 0 < 1 - Real.exp (-beta) := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
      linarith
    have hp1 : 1 - Real.exp (-beta) < 1 := by
      linarith [Real.exp_pos (-beta)]
    have hexp : Real.exp (-beta) < Real.exp (-betaC) :=
      Real.exp_lt_exp.mpr (by linarith)
    apply FK.frp_fkTheta_pos_of_gt_fkPc d hp hp1 (zero_lt_one.trans_le hq)
    have hgt : pc < 1 - Real.exp (-beta) := by
      rw [← hparam]
      linarith
    simpa [pc] using hgt

theorem wiredBeta1Q_eq_fkBetaCriticalQ
    (d : Nat) (q beta0 : Real) (hd : 2 <= d) (hq : 1 <= q)
    (hbeta0 : 0 < betaFKThetaQ d q hq beta0) :
    wiredBeta1Q d q beta0 = fkBetaCriticalQ d q :=
  (betaCriticalQ_eq_wiredBeta1Q d q beta0 hd hq hbeta0).symm.trans
    (betaCriticalQ_eq_fkBetaCriticalQ d q hd hq)


theorem betaFKThetaQ_meanField_above_fkBetaCriticalQ
    (d : Nat) (q beta0 beta : Real) (hd : 2 <= d) (hq : 1 <= q)
    (hbeta0 : 0 < betaFKThetaQ d q hq beta0)
    (hcrit : fkBetaCriticalQ d q < beta) (hupper : beta <= beta0) :
    wiredSharpConstant d beta0 * (beta - fkBetaCriticalQ d q) <=
      betaFKThetaQ d q hq beta := by
  have hthreshold := wiredBeta1Q_eq_fkBetaCriticalQ d q beta0 hd hq hbeta0
  have hcrit' : wiredBeta1Q d q beta0 < beta := by
    rw [hthreshold]
    exact hcrit
  have h := betaFKThetaQ_meanField_lower
    d q beta0 beta hd hq hcrit' hupper
  rwa [hthreshold] at h


theorem wiredOuterInner_subcritical_decay_below_fkBetaCriticalQ
    (d : Nat) (q beta0 beta : Real) (hd : 2 <= d) (hq : 1 <= q)
    (hbeta0 : 0 < betaFKThetaQ d q hq beta0)
    (hbeta : 0 < beta) (hcrit : beta < fkBetaCriticalQ d q) :
    ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 <= n →
      wiredOuterInnerTheta d q beta n <= Real.exp (-((n : Real) / Q)) := by
  let betaMid := (beta + fkBetaCriticalQ d q) / 2
  let delta := (betaMid - beta) / 2
  have hmidLower : beta < betaMid := by dsimp [betaMid]; linarith
  have hmidUpper : betaMid < fkBetaCriticalQ d q := by
    dsimp [betaMid]
    linarith
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hleft : betaMid - 2 * delta = beta := by
    dsimp [delta, betaMid]
    ring
  have hthreshold := wiredBeta1Q_eq_fkBetaCriticalQ d q beta0 hd hq hbeta0
  have hmidBeta0 : betaMid <= beta0 := by
    have hbeta1le := wiredBeta1Q_le_of_betaFKThetaQ_pos d q beta0 hq hbeta0
    rw [hthreshold] at hbeta1le
    exact hmidUpper.le.trans hbeta1le
  obtain ⟨Q, hQ, hdecay⟩ := wiredOuterInner_subcritical_decay_of_threshold
    d q delta betaMid beta0 hq hmidBeta0 hdelta
      (by rw [hleft]; exact hbeta) (by
        change betaMid < wiredBeta1Q d q beta0
        rw [hthreshold]
        exact hmidUpper)
  refine ⟨Q / delta, div_pos hQ hdelta, ?_⟩
  intro n hn
  have h := hdecay n hn
  rw [hleft] at h
  convert h using 1 <;> field_simp <;> ring

end WiredBoxCriticalGeneral
end OSSS
end StatMech
