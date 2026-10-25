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
import Def.StatisticalMechanics.Code.OSSS.WiredBoxCritical.Part2
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace WiredBoxCritical

open Filter

open WiredBoxSharpness

open Lattice FK

open WiredBoxLocalized WiredBoxOffCentre

open MeasureTheory


theorem betaCritical_eq_fkBetaCritical_q2
    (d : Nat) (hd : 2 <= d) :
    sSup (BetaCMatch.bcm_subcriticalSet (betaFKTheta d)) = fkBetaCritical d := by
  let pc := FK.fkPc d 2
  let betaC := fkBetaCritical d
  have hpc0 : 0 < pc := FK.fkPc_pos_of_two_le hd (by norm_num)
  have hpc1 : pc < 1 := FK.fkPc_two_lt_one_of_two_le hd
  have hremain : 0 < 1 - pc := by linarith
  have hremain1 : 1 - pc < 1 := by linarith
  have hbetaC : 0 < betaC := by
    dsimp [betaC, fkBetaCritical]
    exact neg_pos.mpr (Real.log_neg hremain hremain1)
  have hparam : 1 - Real.exp (-betaC) = pc := by
    dsimp [betaC, fkBetaCritical]
    rw [neg_neg, Real.exp_log hremain]
    ring
  apply BetaCMatch.bcm_betaC_eq_threshold (betaFKTheta d) betaC
  · intro beta hbelow
    by_cases hbeta : 0 < beta
    · rw [betaFKTheta_eq d beta hbeta]
      have hp : 0 < 1 - Real.exp (-beta) := by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith
      have hp1 : 1 - Real.exp (-beta) < 1 := by
        linarith [Real.exp_pos (-beta)]
      have hexp : Real.exp (-betaC) < Real.exp (-beta) :=
        Real.exp_lt_exp.mpr (by linarith)
      apply FK.tzp_fkTheta_eq_zero_of_lt_pc hp hp1
      have hlt : 1 - Real.exp (-beta) < pc := by
        rw [← hparam]
        linarith
      simpa [pc] using hlt
    · simp [betaFKTheta, hbeta]
  · intro beta habove
    have hbeta : 0 < beta := hbetaC.trans habove
    rw [betaFKTheta_eq d beta hbeta]
    have hp : 0 < 1 - Real.exp (-beta) := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
      linarith
    have hp1 : 1 - Real.exp (-beta) < 1 := by
      linarith [Real.exp_pos (-beta)]
    have hexp : Real.exp (-beta) < Real.exp (-betaC) :=
      Real.exp_lt_exp.mpr (by linarith)
    apply FK.frp_fkTheta_pos_of_gt_fkPc d hp hp1 (by norm_num)
    have hgt : pc < 1 - Real.exp (-beta) := by
      rw [← hparam]
      linarith
    simpa [pc] using hgt


theorem wiredBeta1_eq_fkBetaCritical_q2
    (d : Nat) (beta0 : Real) (hd : 2 <= d)
    (hbeta0 : 0 < betaFKTheta d beta0) :
    wiredBeta1 d beta0 = fkBetaCritical d :=
  (betaCritical_eq_wiredBeta1_q2 d beta0 hd hbeta0).symm.trans
    (betaCritical_eq_fkBetaCritical_q2 d hd)


end WiredBoxCritical
end OSSS
end StatMech
