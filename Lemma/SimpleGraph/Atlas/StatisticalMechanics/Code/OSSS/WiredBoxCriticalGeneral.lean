import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxCriticalGeneral.Part3
open StatMech StatMech.OSSS StatMech.OSSS.WiredBoxCriticalGeneral


/--
[betaFKThetaQ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean)
-/
@[path]
private lemma betaFKThetaQ_eq_eq
  {d : Nat}
  {q : Real}
  {beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  betaFKThetaQ d q hq beta = FK.fkTheta d (by have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0) linarith : 0 < 1 - Real.exp (-beta)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (zero_lt_one.trans_le hq) (q := q) := by
-- proof
  apply StatMech.OSSS.WiredBoxCriticalGeneral.betaFKThetaQ_eq d q hq beta hbeta

/--
[betaFKThetaQ_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean)
-/
@[path]
private lemma betaFKThetaQ_nonneg_eq
  {d : Nat}
  {q : Real}
  {beta : Real}
-- given
  (hq : 1 <= q) :
-- imply
  0 <= betaFKThetaQ d q hq beta := by
-- proof
  apply StatMech.OSSS.WiredBoxCriticalGeneral.betaFKThetaQ_nonneg d q hq beta

/--
[wiredBeta1Q_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean)
-/
@[path]
private lemma wiredBeta1Q_nonneg_eq
  {d : Nat}
  {q beta0 : Real}
-- given
  (hd : 2 <= d)
  (hq : 1 <= q) :
-- imply
  0 <= wiredBeta1Q d q beta0 := by
-- proof
  apply StatMech.OSSS.WiredBoxCriticalGeneral.wiredBeta1Q_nonneg d q beta0 hd hq

/--
[wiredNormalizedTheta_tendsto_betaFKThetaQ_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean)
-/
@[path]
private lemma wiredNormalizedTheta_tendsto_betaFKThetaQ_div_eq
  {d : Nat}
  {q beta0 beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  Tendsto (fun n => wiredNormalizedTheta d q beta0 n beta) atTop (nhds (betaFKThetaQ d q hq beta / wiredSharpConstant d beta0)) := by
-- proof
  apply StatMech.OSSS.WiredBoxCriticalGeneral.wiredNormalizedTheta_tendsto_betaFKThetaQ_div d q beta0 beta hq hbeta

/--
[betaFKThetaQ_difference_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean)
-/
@[path]
private lemma betaFKThetaQ_difference_lower_eq
  {d : Nat}
  {q beta0 beta' beta : Real}
-- given
  (hd : 2 <= d)
  (hq : 1 <= q)
  (hcrit : wiredBeta1Q d q beta0 < beta')
  (hbeta : beta' <= beta)
  (hupper : beta <= beta0) :
-- imply
  beta - beta' <= betaFKThetaQ d q hq beta / wiredSharpConstant d beta0 - betaFKThetaQ d q hq beta' / wiredSharpConstant d beta0 := by
-- proof
  apply StatMech.OSSS.WiredBoxCriticalGeneral.betaFKThetaQ_difference_lower d q beta0 beta' beta hd hq hcrit hbeta hupper

/--
[betaFKThetaQ_meanField_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean)
-/
@[path]
private lemma betaFKThetaQ_meanField_lower_eq
  {d : Nat}
  {q beta0 beta : Real}
-- given
  (hd : 2 <= d)
  (hq : 1 <= q)
  (hcrit : wiredBeta1Q d q beta0 < beta)
  (hupper : beta <= beta0) :
-- imply
  wiredSharpConstant d beta0 * (beta - wiredBeta1Q d q beta0) <= betaFKThetaQ d q hq beta := by
-- proof
  apply StatMech.OSSS.WiredBoxCriticalGeneral.betaFKThetaQ_meanField_lower d q beta0 beta hd hq hcrit hupper

/--
[betaFKThetaQ_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean)
-/
@[path]
private lemma betaFKThetaQ_mono_eq
  {d : Nat}
  {q : Real}
-- given
  (hq : 1 <= q) :
-- imply
  Monotone (betaFKThetaQ d q hq) := by
-- proof
  apply StatMech.OSSS.WiredBoxCriticalGeneral.betaFKThetaQ_mono d q hq

/--
[wiredBeta1Q_le_of_betaFKThetaQ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean)
-/
@[path]
private lemma wiredBeta1Q_le_of_betaFKThetaQ_pos_eq
  {d : Nat}
  {q beta0 : Real}
-- given
  (hq : 1 <= q)
  (hbeta0 : 0 < betaFKThetaQ d q hq beta0) :
-- imply
  wiredBeta1Q d q beta0 <= beta0 := by
-- proof
  apply StatMech.OSSS.WiredBoxCriticalGeneral.wiredBeta1Q_le_of_betaFKThetaQ_pos d q beta0 hq hbeta0

/--
[betaFKThetaQ_eq_zero_below_wiredBeta1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean)
-/
@[path]
private lemma betaFKThetaQ_eq_zero_below_wiredBeta1_eq
  {d : Nat}
  {q beta0 beta : Real}
-- given
  (hd : 2 <= d)
  (hq : 1 <= q)
  (hbeta0 : 0 < betaFKThetaQ d q hq beta0)
  (hlt : beta < wiredBeta1Q d q beta0) :
-- imply
  betaFKThetaQ d q hq beta = 0 := by
-- proof
  apply StatMech.OSSS.WiredBoxCriticalGeneral.betaFKThetaQ_eq_zero_below_wiredBeta1 d q beta0 beta hd hq hbeta0 hlt

/--
[betaFKThetaQ_pos_above_wiredBeta1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean)
-/
@[path]
private lemma betaFKThetaQ_pos_above_wiredBeta1_eq
  {d : Nat}
  {q beta0 beta : Real}
-- given
  (hd : 2 <= d)
  (hq : 1 <= q)
  (hbeta0 : 0 < betaFKThetaQ d q hq beta0)
  (hlt : wiredBeta1Q d q beta0 < beta) :
-- imply
  0 < betaFKThetaQ d q hq beta := by
-- proof
  apply StatMech.OSSS.WiredBoxCriticalGeneral.betaFKThetaQ_pos_above_wiredBeta1 d q beta0 beta hd hq hbeta0 hlt

/--
[betaCriticalQ_eq_wiredBeta1Q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean)
-/
@[path]
private lemma betaCriticalQ_eq_wiredBeta1Q_eq
  {d : Nat}
  {q beta0 : Real}
-- given
  (hd : 2 <= d)
  (hq : 1 <= q)
  (hbeta0 : 0 < betaFKThetaQ d q hq beta0) :
-- imply
  sSup (BetaCMatch.bcm_subcriticalSet (betaFKThetaQ d q hq)) = wiredBeta1Q d q beta0 := by
-- proof
  apply StatMech.OSSS.WiredBoxCriticalGeneral.betaCriticalQ_eq_wiredBeta1Q d q beta0 hd hq hbeta0

/--
[betaCriticalQ_eq_fkBetaCriticalQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean)
-/
@[path]
private lemma betaCriticalQ_eq_fkBetaCriticalQ_eq
  {d : Nat}
  {q : Real}
-- given
  (hd : 2 <= d)
  (hq : 1 <= q) :
-- imply
  sSup (BetaCMatch.bcm_subcriticalSet (betaFKThetaQ d q hq)) = fkBetaCriticalQ d q := by
-- proof
  apply StatMech.OSSS.WiredBoxCriticalGeneral.betaCriticalQ_eq_fkBetaCriticalQ d q hd hq

/--
[wiredBeta1Q_eq_fkBetaCriticalQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean)
-/
@[path]
private lemma wiredBeta1Q_eq_fkBetaCriticalQ_eq
  {d : Nat}
  {q beta0 : Real}
-- given
  (hd : 2 <= d)
  (hq : 1 <= q)
  (hbeta0 : 0 < betaFKThetaQ d q hq beta0) :
-- imply
  wiredBeta1Q d q beta0 = fkBetaCriticalQ d q := by
-- proof
  apply StatMech.OSSS.WiredBoxCriticalGeneral.wiredBeta1Q_eq_fkBetaCriticalQ d q beta0 hd hq hbeta0

/--
[betaFKThetaQ_meanField_above_fkBetaCriticalQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean)
-/
@[path]
private lemma betaFKThetaQ_meanField_above_fkBetaCriticalQ_eq
  {d : Nat}
  {q beta0 beta : Real}
-- given
  (hd : 2 <= d)
  (hq : 1 <= q)
  (hbeta0 : 0 < betaFKThetaQ d q hq beta0)
  (hcrit : fkBetaCriticalQ d q < beta)
  (hupper : beta <= beta0) :
-- imply
  wiredSharpConstant d beta0 * (beta - fkBetaCriticalQ d q) <= betaFKThetaQ d q hq beta := by
-- proof
  apply StatMech.OSSS.WiredBoxCriticalGeneral.betaFKThetaQ_meanField_above_fkBetaCriticalQ d q beta0 beta hd hq hbeta0 hcrit hupper

/--
[wiredOuterInner_subcritical_decay_below_fkBetaCriticalQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean)
-/
@[path]
private lemma wiredOuterInner_subcritical_decay_below_fkBetaCriticalQ_eq
  {d : Nat}
  {q beta0 beta : Real}
-- given
  (hd : 2 <= d)
  (hq : 1 <= q)
  (hbeta0 : 0 < betaFKThetaQ d q hq beta0)
  (hbeta : 0 < beta)
  (hcrit : beta < fkBetaCriticalQ d q) :
-- imply
  ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 <= n → wiredOuterInnerTheta d q beta n <= Real.exp (-((n : Real) / Q)) := by
-- proof
  apply StatMech.OSSS.WiredBoxCriticalGeneral.wiredOuterInner_subcritical_decay_below_fkBetaCriticalQ d q beta0 beta hd hq hbeta0 hbeta hcrit

/--
[fkCriticalBetaQ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean)
-/
@[path]
private lemma fkCriticalBetaQ_pos_eq
  {d : Nat}
  {q : Real}
-- given
  (hd : 2 <= d)
  (hq : 1 <= q) :
-- imply
  0 < fkCriticalBetaQ d q := by
-- proof
  apply StatMech.OSSS.WiredBoxCriticalGeneral.fkCriticalBetaQ_pos d q hd hq

/--
[fkCriticalBetaQ_param](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean)
-/
@[path]
private lemma fkCriticalBetaQ_param_eq
  {d : Nat}
  {q : Real}
-- given
  (hd : 2 <= d)
  (hq : 1 <= q) :
-- imply
  1 - Real.exp (-fkCriticalBetaQ d q) = FK.fkPc d q := by
-- proof
  apply StatMech.OSSS.WiredBoxCriticalGeneral.fkCriticalBetaQ_param d q hd hq

/--
[betaToP_lt_fkPc_of_lt_fkCriticalBetaQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean)
-/
@[path]
private lemma betaToP_lt_fkPc_of_lt_fkCriticalBetaQ_eq
  {d : Nat}
  {q : Real}
  {beta : Real}
-- given
  (hd : 2 <= d)
  (hq : 1 <= q)
  (hbeta : beta < fkCriticalBetaQ d q) :
-- imply
  1 - Real.exp (-beta) < FK.fkPc d q := by
-- proof
  apply StatMech.OSSS.WiredBoxCriticalGeneral.betaToP_lt_fkPc_of_lt_fkCriticalBetaQ d q hd hq hbeta

/--
[fkPc_lt_betaToP_of_fkCriticalBetaQ_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean)
-/
@[path]
private lemma fkPc_lt_betaToP_of_fkCriticalBetaQ_lt_eq
  {d : Nat}
  {q : Real}
  {beta : Real}
-- given
  (hd : 2 <= d)
  (hq : 1 <= q)
  (hbeta : fkCriticalBetaQ d q < beta) :
-- imply
  FK.fkPc d q < 1 - Real.exp (-beta) := by
-- proof
  apply StatMech.OSSS.WiredBoxCriticalGeneral.fkPc_lt_betaToP_of_fkCriticalBetaQ_lt d q hd hq hbeta

/--
[wiredBeta1Q_eq_fkCriticalBetaQ_of_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean)
-/
@[path]
private lemma wiredBeta1Q_eq_fkCriticalBetaQ_of_ge_eq
  {d : Nat}
  {q beta0 : Real}
-- given
  (hd : 2 <= d)
  (hq : 1 <= q)
  (hbeta0 : fkCriticalBetaQ d q <= beta0) :
-- imply
  wiredBeta1Q d q beta0 = fkCriticalBetaQ d q := by
-- proof
  apply StatMech.OSSS.WiredBoxCriticalGeneral.wiredBeta1Q_eq_fkCriticalBetaQ_of_ge d q beta0 hd hq hbeta0

/--
[wiredOuterInner_exponential_decay_below_fkCriticalBetaQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean)
-/
@[path]
private lemma wiredOuterInner_exponential_decay_below_fkCriticalBetaQ_eq
  {d : Nat}
  {q beta : Real}
-- given
  (hd : 2 <= d)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hsub : beta < fkCriticalBetaQ d q) :
-- imply
  ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 <= n -> wiredOuterInnerTheta d q beta n <= Real.exp (-((n : Real) / Q * ((fkCriticalBetaQ d q - beta) / 4))) := by
-- proof
  apply StatMech.OSSS.WiredBoxCriticalGeneral.wiredOuterInner_exponential_decay_below_fkCriticalBetaQ d q beta hd hq hbeta hsub

/--
[betaFKThetaQ_meanField_above_fkCriticalBetaQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean)
-/
@[path]
private lemma betaFKThetaQ_meanField_above_fkCriticalBetaQ_eq
  {d : Nat}
  {q beta : Real}
-- given
  (hd : 2 <= d)
  (hq : 1 <= q)
  (hsuper : fkCriticalBetaQ d q < beta) :
-- imply
  wiredSharpConstant d beta * (beta - fkCriticalBetaQ d q) <= betaFKThetaQ d q hq beta := by
-- proof
  apply StatMech.OSSS.WiredBoxCriticalGeneral.betaFKThetaQ_meanField_above_fkCriticalBetaQ d q beta hd hq hsuper

/--
[fkSharpness_homogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean)
-/
@[path]
private lemma fkSharpness_homogeneous_eq
  {d : Nat}
  {q : Real}
-- given
  (hd : 2 <= d)
  (hq : 1 <= q) :
-- imply
  (forall beta, fkCriticalBetaQ d q <= beta -> wiredSharpConstant d beta * (beta - fkCriticalBetaQ d q) <= betaFKThetaQ d q hq beta) ∧ (forall beta, 0 < beta -> beta < fkCriticalBetaQ d q -> ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 <= n -> wiredOuterInnerTheta d q beta n <= Real.exp (-((n : Real) / Q * ((fkCriticalBetaQ d q - beta) / 4)))) := by
-- proof
  apply StatMech.OSSS.WiredBoxCriticalGeneral.fkSharpness_homogeneous d q hd hq


-- created on 2026-10-23
