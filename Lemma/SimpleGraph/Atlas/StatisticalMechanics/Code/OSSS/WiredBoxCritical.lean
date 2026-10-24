import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.WiredBoxCritical
open StatMech StatMech.OSSS StatMech.OSSS.WiredBoxCritical


/--
[wiredOuterInnerTheta_eq_wiredFiniteMeasure_double](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma wiredOuterInnerTheta_eq_wiredFiniteMeasure_double_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  wiredOuterInnerTheta d q beta n = (FK.wiredFiniteMeasure d (2 * n) (by have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0) linarith : 0 < 1 - Real.exp (-beta)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real (FK.boxBdryConnEvent d n) := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.wiredOuterInnerTheta_eq_wiredFiniteMeasure_double d n hn q beta hq hbeta

/--
[wiredOuterInnerTheta_tendsto_fkTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma wiredOuterInnerTheta_tendsto_fkTheta_eq
  {d : Nat}
  {q beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  Tendsto (fun n => wiredOuterInnerTheta d q beta n) atTop (nhds (FK.fkTheta d (by have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0) linarith : 0 < 1 - Real.exp (-beta)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (zero_lt_one.trans_le hq) (q := q))) := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.wiredOuterInnerTheta_tendsto_fkTheta d q beta hq hbeta

/--
[wiredThresholdTheta_tendsto_fkTheta_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma wiredThresholdTheta_tendsto_fkTheta_div_eq
  {d : Nat}
  {q beta0 beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  Tendsto (fun n => wiredThresholdTheta d q beta0 n beta) atTop (nhds (FK.fkTheta d (by have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0) linarith : 0 < 1 - Real.exp (-beta)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (zero_lt_one.trans_le hq) (q := q) / wiredSharpConstant d beta0)) := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.wiredThresholdTheta_tendsto_fkTheta_div d q beta0 beta hq hbeta

/--
[wiredThresholdSet_mem_of_fkTheta_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma wiredThresholdSet_mem_of_fkTheta_pos_eq
  {d : Nat}
  {q beta0 beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hTheta : 0 < FK.fkTheta d (by have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0) linarith : 0 < 1 - Real.exp (-beta)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (zero_lt_one.trans_le hq) (q := q)) :
-- imply
  beta ∈ BetaThresholdBound.thresholdSet (fun b n => IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n b) := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.wiredThresholdSet_mem_of_fkTheta_pos d q beta0 beta hq hbeta hTheta

/--
[wiredThresholdSet_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma wiredThresholdSet_nonempty_eq
  {d : Nat}
  {q beta0 : Real}
-- given
  (hd : 2 <= d)
  (hq : 1 <= q) :
-- imply
  (BetaThresholdBound.thresholdSet (fun b n => IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n b)).Nonempty := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.wiredThresholdSet_nonempty d q beta0 hd hq

/--
[betaFKTheta_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma betaFKTheta_eq_eq
  {d : Nat}
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  betaFKTheta d beta = FK.fkTheta d (by have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0) linarith : 0 < 1 - Real.exp (-beta)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (by norm_num : (0 : Real) < 2) (q := 2) := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.betaFKTheta_eq d beta hbeta

/--
[betaFKTheta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma betaFKTheta_nonneg_eq
  {d : Nat}
  {beta : Real} :
-- imply
  0 <= betaFKTheta d beta := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.betaFKTheta_nonneg d beta

/--
[betaFKTheta_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma betaFKTheta_mono_eq
  {d : Nat} :
-- imply
  Monotone (betaFKTheta d) := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.betaFKTheta_mono d

/--
[wiredThresholdSet_nonempty_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma wiredThresholdSet_nonempty_q2_eq
  {d : Nat}
  {beta0 : Real}
-- given
  (hd : 2 <= d) :
-- imply
  (BetaThresholdBound.thresholdSet (fun b n => IntegrationSubcritical.Sig (wiredThresholdTheta d 2 beta0) n b)).Nonempty := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.wiredThresholdSet_nonempty_q2 d beta0 hd

/--
[wiredBeta1_nonneg_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma wiredBeta1_nonneg_q2_eq
  {d : Nat}
  {beta0 : Real}
-- given
  (hd : 2 <= d) :
-- imply
  0 <= wiredBeta1 d beta0 := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.wiredBeta1_nonneg_q2 d beta0 hd

/--
[wiredNormalizedTheta_tendsto_betaFKTheta_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma wiredNormalizedTheta_tendsto_betaFKTheta_div_eq
  {d : Nat}
  {beta0 beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  Tendsto (fun n => wiredNormalizedTheta d 2 beta0 n beta) atTop (nhds (betaFKTheta d beta / wiredSharpConstant d beta0)) := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.wiredNormalizedTheta_tendsto_betaFKTheta_div d beta0 beta hbeta

/--
[betaFKTheta_difference_lower_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma betaFKTheta_difference_lower_q2_eq
  {d : Nat}
  {beta0 beta' beta : Real}
-- given
  (hd : 2 <= d)
  (hcrit : wiredBeta1 d beta0 < beta')
  (hbeta : beta' <= beta)
  (hupper : beta <= beta0) :
-- imply
  beta - beta' <= betaFKTheta d beta / wiredSharpConstant d beta0 - betaFKTheta d beta' / wiredSharpConstant d beta0 := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.betaFKTheta_difference_lower_q2 d beta0 beta' beta hd hcrit hbeta hupper

/--
[betaFKTheta_meanField_lower_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma betaFKTheta_meanField_lower_q2_eq
  {d : Nat}
  {beta0 beta : Real}
-- given
  (hd : 2 <= d)
  (hcrit : wiredBeta1 d beta0 < beta)
  (hupper : beta <= beta0) :
-- imply
  wiredSharpConstant d beta0 * (beta - wiredBeta1 d beta0) <= betaFKTheta d beta := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.betaFKTheta_meanField_lower_q2 d beta0 beta hd hcrit hupper

/--
[wiredBeta1_le_of_betaFKTheta_pos_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma wiredBeta1_le_of_betaFKTheta_pos_q2_eq
  {d : Nat}
  {beta0 : Real}
-- given
  (hbeta0 : 0 < betaFKTheta d beta0) :
-- imply
  wiredBeta1 d beta0 <= beta0 := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.wiredBeta1_le_of_betaFKTheta_pos_q2 d beta0 hbeta0

/--
[betaFKTheta_eq_zero_below_wiredBeta1_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma betaFKTheta_eq_zero_below_wiredBeta1_q2_eq
  {d : Nat}
  {beta0 beta : Real}
-- given
  (hd : 2 <= d)
  (hbeta0 : 0 < betaFKTheta d beta0)
  (hlt : beta < wiredBeta1 d beta0) :
-- imply
  betaFKTheta d beta = 0 := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.betaFKTheta_eq_zero_below_wiredBeta1_q2 d beta0 beta hd hbeta0 hlt

/--
[betaFKTheta_pos_above_wiredBeta1_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma betaFKTheta_pos_above_wiredBeta1_q2_eq
  {d : Nat}
  {beta0 beta : Real}
-- given
  (hd : 2 <= d)
  (hbeta0 : 0 < betaFKTheta d beta0)
  (hlt : wiredBeta1 d beta0 < beta) :
-- imply
  0 < betaFKTheta d beta := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.betaFKTheta_pos_above_wiredBeta1_q2 d beta0 beta hd hbeta0 hlt

/--
[betaCritical_eq_wiredBeta1_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma betaCritical_eq_wiredBeta1_q2_eq
  {d : Nat}
  {beta0 : Real}
-- given
  (hd : 2 <= d)
  (hbeta0 : 0 < betaFKTheta d beta0) :
-- imply
  sSup (BetaCMatch.bcm_subcriticalSet (betaFKTheta d)) = wiredBeta1 d beta0 := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.betaCritical_eq_wiredBeta1_q2 d beta0 hd hbeta0

/--
[betaCritical_eq_fkBetaCritical_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma betaCritical_eq_fkBetaCritical_q2_eq
  {d : Nat}
-- given
  (hd : 2 <= d) :
-- imply
  sSup (BetaCMatch.bcm_subcriticalSet (betaFKTheta d)) = fkBetaCritical d := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.betaCritical_eq_fkBetaCritical_q2 d hd

/--
[wiredBeta1_eq_fkBetaCritical_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma wiredBeta1_eq_fkBetaCritical_q2_eq
  {d : Nat}
  {beta0 : Real}
-- given
  (hd : 2 <= d)
  (hbeta0 : 0 < betaFKTheta d beta0) :
-- imply
  wiredBeta1 d beta0 = fkBetaCritical d := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.wiredBeta1_eq_fkBetaCritical_q2 d beta0 hd hbeta0

/--
[fkCriticalBeta_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma fkCriticalBeta_pos_eq
  {d : Nat}
-- given
  (hd : 2 <= d) :
-- imply
  0 < fkCriticalBeta d := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.fkCriticalBeta_pos d hd

/--
[fkCriticalBeta_param](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma fkCriticalBeta_param_eq
  {d : Nat}
-- given
  (hd : 2 <= d) :
-- imply
  1 - Real.exp (-fkCriticalBeta d) = FK.fkPc d 2 := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.fkCriticalBeta_param d hd

/--
[betaToP_lt_fkPc_of_lt_fkCriticalBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma betaToP_lt_fkPc_of_lt_fkCriticalBeta_eq
  {d : Nat}
  {beta : Real}
-- given
  (hd : 2 <= d)
  (hbeta : beta < fkCriticalBeta d) :
-- imply
  1 - Real.exp (-beta) < FK.fkPc d 2 := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.betaToP_lt_fkPc_of_lt_fkCriticalBeta d hd hbeta

/--
[fkPc_lt_betaToP_of_fkCriticalBeta_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma fkPc_lt_betaToP_of_fkCriticalBeta_lt_eq
  {d : Nat}
  {beta : Real}
-- given
  (hd : 2 <= d)
  (hbeta : fkCriticalBeta d < beta) :
-- imply
  FK.fkPc d 2 < 1 - Real.exp (-beta) := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.fkPc_lt_betaToP_of_fkCriticalBeta_lt d hd hbeta

/--
[wiredBeta1_eq_fkCriticalBeta_q2_of_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma wiredBeta1_eq_fkCriticalBeta_q2_of_ge_eq
  {d : Nat}
  {beta0 : Real}
-- given
  (hd : 2 <= d)
  (hbeta0 : fkCriticalBeta d <= beta0) :
-- imply
  wiredBeta1 d beta0 = fkCriticalBeta d := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.wiredBeta1_eq_fkCriticalBeta_q2_of_ge d beta0 hd hbeta0

/--
[wiredBeta1_eq_fkCriticalBeta_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma wiredBeta1_eq_fkCriticalBeta_q2_eq
  {d : Nat}
-- given
  (hd : 2 <= d) :
-- imply
  wiredBeta1 d (fkCriticalBeta d) = fkCriticalBeta d := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.wiredBeta1_eq_fkCriticalBeta_q2 d hd

/--
[wiredOuterInner_exponential_decay_below_fkCriticalBeta_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma wiredOuterInner_exponential_decay_below_fkCriticalBeta_q2_eq
  {d : Nat}
  {beta : Real}
-- given
  (hd : 2 <= d)
  (hbeta : 0 < beta)
  (hsub : beta < fkCriticalBeta d) :
-- imply
  ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 <= n -> wiredOuterInnerTheta d 2 beta n <= Real.exp (-((n : Real) / Q * ((fkCriticalBeta d - beta) / 4))) := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.wiredOuterInner_exponential_decay_below_fkCriticalBeta_q2 d beta hd hbeta hsub

/--
[betaFKTheta_meanField_above_fkCriticalBeta_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean)
-/
@[path]
private lemma betaFKTheta_meanField_above_fkCriticalBeta_q2_eq
  {d : Nat}
  {beta : Real}
-- given
  (hd : 2 <= d)
  (hsuper : fkCriticalBeta d < beta) :
-- imply
  wiredSharpConstant d beta * (beta - fkCriticalBeta d) <= betaFKTheta d beta := by
-- proof
  apply StatMech.OSSS.WiredBoxCritical.betaFKTheta_meanField_above_fkCriticalBeta_q2 d beta hd hsuper


-- created on 2026-10-23
