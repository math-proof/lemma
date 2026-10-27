import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxSharpness
open StatMech StatMech.OSSS StatMech.OSSS.WiredBoxSharpness


/--
[wiredSharpConstant_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredSharpConstant_pos_eq
  {d : Nat}
  {beta0 : Real} :
-- imply
  0 < wiredSharpConstant d beta0 := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredSharpConstant_pos d beta0

/--
[wiredSharpConstant_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredSharpConstant_le_one_eq
  {d : Nat}
  {beta0 : Real}
-- given
  (hbeta0 : 0 <= beta0) :
-- imply
  wiredSharpConstant d beta0 <= 1 := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredSharpConstant_le_one d beta0 hbeta0

/--
[one_le_inv_wiredSharpConstant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma one_le_inv_wiredSharpConstant_eq
  {d : Nat}
  {beta0 : Real}
-- given
  (hbeta0 : 0 <= beta0) :
-- imply
  1 <= 1 / wiredSharpConstant d beta0 := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.one_le_inv_wiredSharpConstant d beta0 hbeta0

/--
[wiredOuterInnerTheta_eq_activeBCMean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredOuterInnerTheta_eq_activeBCMean_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hn : 1 <= n) :
-- imply
  wiredOuterInnerTheta d q beta n = activeBCMean (boxGraph d (2 * n)) (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n)) (betaParams (fun _ => 1) beta) q (innerCrossInd d n) := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredOuterInnerTheta_eq_activeBCMean d n hn q beta

/--
[hasDerivAt_wiredOuterInnerTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma hasDerivAt_wiredOuterInnerTheta_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  HasDerivAt (fun b => wiredOuterInnerTheta d q b n) (wiredOuterInnerThetaPrime d n q beta) beta := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.hasDerivAt_wiredOuterInnerTheta d n hn q beta hq hbeta

/--
[wiredOuterInnerSig_eq_integrationSig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredOuterInnerSig_eq_integrationSig_eq
  {d n : Nat}
  {q beta : Real} :
-- imply
  wiredOuterInnerSig d n q beta = IntegrationSubcritical.Sig (fun k b => wiredOuterInnerTheta d q b k) n beta := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredOuterInnerSig_eq_integrationSig d n q beta

/--
[normalizedSig_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma normalizedSig_eq_eq
  {d n : Nat}
  {q beta0 beta : Real} :
-- imply
  IntegrationSubcritical.Sig (wiredNormalizedTheta d q beta0) n beta = wiredOuterInnerSig d n q beta / wiredSharpConstant d beta0 := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.normalizedSig_eq d n q beta0 beta

/--
[wiredThresholdTheta_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredThresholdTheta_of_pos_eq
  {d n : Nat}
  {q beta0 beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  wiredThresholdTheta d q beta0 n beta = wiredNormalizedTheta d q beta0 n beta := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredThresholdTheta_of_pos d n q beta0 beta hbeta

/--
[thresholdSig_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma thresholdSig_of_pos_eq
  {d n : Nat}
  {q beta0 beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n beta = IntegrationSubcritical.Sig (wiredNormalizedTheta d q beta0) n beta := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.thresholdSig_of_pos d n q beta0 beta hbeta

/--
[thresholdSig_of_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma thresholdSig_of_nonpos_eq
  {d n : Nat}
  {q beta0 beta : Real}
-- given
  (hn : 1 <= n)
  (hbeta : beta <= 0) :
-- imply
  IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n beta = 1 / wiredSharpConstant d beta0 := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.thresholdSig_of_nonpos d n hn q beta0 beta hbeta

/--
[wiredThresholdSet_bddBelow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredThresholdSet_bddBelow_eq
  {d : Nat}
  {q beta0 : Real} :
-- imply
  BddBelow (BetaThresholdBound.thresholdSet (fun b n => IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n b)) := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredThresholdSet_bddBelow d q beta0

/--
[wiredOuterInnerTheta_differential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredOuterInnerTheta_differential_eq
  {d n : Nat}
  {q beta beta0 : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hbeta0 : beta <= beta0) :
-- imply
  wiredSharpConstant d beta0 * (((n : Real) / wiredOuterInnerSig d n q beta) * wiredOuterInnerTheta d q beta n) <= wiredOuterInnerThetaPrime d n q beta := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredOuterInnerTheta_differential d n hn q beta beta0 hq hbeta hbeta0

/--
[hasDerivAt_wiredNormalizedTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma hasDerivAt_wiredNormalizedTheta_eq
  {d n : Nat}
  {q beta0 beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  HasDerivAt (wiredNormalizedTheta d q beta0 n) (wiredNormalizedThetaPrime d q beta0 n beta) beta := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.hasDerivAt_wiredNormalizedTheta d n hn q beta0 beta hq hbeta

/--
[wiredNormalizedTheta_differential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredNormalizedTheta_differential_eq
  {d n : Nat}
  {q beta beta0 : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hbeta0 : beta <= beta0) :
-- imply
  (((n : Real) / IntegrationSubcritical.Sig (wiredNormalizedTheta d q beta0) n beta) * wiredNormalizedTheta d q beta0 n beta) <= wiredNormalizedThetaPrime d q beta0 n beta := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredNormalizedTheta_differential d n hn q beta beta0 hq hbeta hbeta0

/--
[wiredOuterInnerTheta_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredOuterInnerTheta_le_one_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  wiredOuterInnerTheta d q beta n <= 1 := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredOuterInnerTheta_le_one d n q beta hq hbeta

/--
[wiredNormalizedTheta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredNormalizedTheta_nonneg_eq
  {d n : Nat}
  {q beta0 beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 <= wiredNormalizedTheta d q beta0 n beta := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredNormalizedTheta_nonneg d n q beta0 beta hq hbeta

/--
[wiredNormalizedTheta_le_invConstant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredNormalizedTheta_le_invConstant_eq
  {d n : Nat}
  {q beta0 beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  wiredNormalizedTheta d q beta0 n beta <= 1 / wiredSharpConstant d beta0 := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredNormalizedTheta_le_invConstant d n q beta0 beta hq hbeta

/--
[normalizedSig_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma normalizedSig_pos_eq
  {d n : Nat}
  {q beta0 beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 < IntegrationSubcritical.Sig (wiredNormalizedTheta d q beta0) n beta := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.normalizedSig_pos d n hn q beta0 beta hq hbeta

/--
[wiredOuterInnerThetaPrime_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredOuterInnerThetaPrime_nonneg_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 <= wiredOuterInnerThetaPrime d n q beta := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredOuterInnerThetaPrime_nonneg d n hn q beta hq hbeta

/--
[wiredNormalizedThetaPrime_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredNormalizedThetaPrime_nonneg_eq
  {d n : Nat}
  {q beta0 beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 <= wiredNormalizedThetaPrime d q beta0 n beta := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredNormalizedThetaPrime_nonneg d n hn q beta0 beta hq hbeta

/--
[wiredNormalizedTheta_mono_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredNormalizedTheta_mono_beta_eq
  {d n : Nat}
  {q beta0 y x : Real}
-- given
  (hq : 1 <= q)
  (hy : 0 < y)
  (hyx : y <= x) :
-- imply
  wiredNormalizedTheta d q beta0 n y <= wiredNormalizedTheta d q beta0 n x := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredNormalizedTheta_mono_beta d n q beta0 y x hq hy hyx

/--
[wiredThresholdTheta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredThresholdTheta_nonneg_eq
  {d n : Nat}
  {q beta0 beta : Real}
-- given
  (hq : 1 <= q) :
-- imply
  0 <= wiredThresholdTheta d q beta0 n beta := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredThresholdTheta_nonneg d n q beta0 beta hq

/--
[wiredThresholdTheta_le_invConstant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredThresholdTheta_le_invConstant_eq
  {d n : Nat}
  {q beta0 beta : Real}
-- given
  (hq : 1 <= q) :
-- imply
  wiredThresholdTheta d q beta0 n beta <= 1 / wiredSharpConstant d beta0 := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredThresholdTheta_le_invConstant d n q beta0 beta hq

/--
[wiredThresholdTheta_mono_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredThresholdTheta_mono_beta_eq
  {d n : Nat}
  {q beta0 a b : Real}
-- given
  (hq : 1 <= q)
  (hab : a <= b) :
-- imply
  wiredThresholdTheta d q beta0 n a <= wiredThresholdTheta d q beta0 n b := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredThresholdTheta_mono_beta d n q beta0 a b hq hab

/--
[thresholdSig_mono_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma thresholdSig_mono_beta_eq
  {d n : Nat}
  {q beta0 : Real}
  {a b : Real}
-- given
  (hq : 1 <= q)
  (hab : a <= b) :
-- imply
  IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n a <= IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n b := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.thresholdSig_mono_beta d n q beta0 hq hab

/--
[thresholdSig_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma thresholdSig_pos_eq
  {d n : Nat}
  {q beta0 beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q) :
-- imply
  0 < IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n beta := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.thresholdSig_pos d n hn q beta0 beta hq

/--
[thresholdSig_le_linear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma thresholdSig_le_linear_eq
  {d n : Nat}
  {q beta0 beta : Real}
-- given
  (hq : 1 <= q) :
-- imply
  IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n beta <= (1 / wiredSharpConstant d beta0) * (n : Real) := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.thresholdSig_le_linear d n q beta0 beta hq

/--
[thresholdLogRatio_bddAbove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma thresholdLogRatio_bddAbove_eq
  {d : Nat}
  {q beta0 beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta0 : 0 <= beta0) :
-- imply
  Filter.IsBoundedUnder (fun x y : Real => x <= y) Filter.atTop (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n beta)) := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.thresholdLogRatio_bddAbove d q beta0 beta hq hbeta0

/--
[thresholdLogRatio_isCobounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma thresholdLogRatio_isCobounded_eq
  {d : Nat}
  {q beta0 beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta0 : 0 <= beta0) :
-- imply
  Filter.IsCoboundedUnder (fun x y : Real => x <= y) Filter.atTop (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n beta)) := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.thresholdLogRatio_isCobounded d q beta0 beta hq hbeta0

/--
[wiredThresholdSet_upward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredThresholdSet_upward_eq
  {d : Nat}
  {q beta0 : Real}
  {a b : Real}
-- given
  (hq : 1 <= q)
  (hbeta0 : 0 <= beta0)
  (hab : a <= b)
  (ha : a ∈ BetaThresholdBound.thresholdSet (fun x n => IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n x)) :
-- imply
  b ∈ BetaThresholdBound.thresholdSet (fun x n => IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n x) := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredThresholdSet_upward d q beta0 hq hbeta0 hab ha

/--
[logRatio_sum_tendsto_one_of_tendsto_pos_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma logRatio_sum_tendsto_one_of_tendsto_pos_active_eq
  {L : Real}
-- given
  (u : Nat -> Real)
  (hL : 0 < L)
  (hu : Filter.Tendsto u Filter.atTop (nhds L)) :
-- imply
  Filter.Tendsto (BetaThresholdBound.logRatio (fun n => ∑ k ∈ Finset.range n, u k)) Filter.atTop (nhds 1) := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.logRatio_sum_tendsto_one_of_tendsto_pos_active u L hL hu

/--
[thresholdSet_mem_of_tendsto_pos_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma thresholdSet_mem_of_tendsto_pos_active_eq
  {L : Real}
-- given
  (f : Nat -> Real)
  (hL : 0 < L)
  (hf : Filter.Tendsto f Filter.atTop (nhds L)) :
-- imply
  (0 : Real) ∈ BetaThresholdBound.thresholdSet (fun _ n => ∑ k ∈ Finset.range n, f k) := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.thresholdSet_mem_of_tendsto_pos_active f L hL hf

/--
[wiredOuterInner_subcritical_decay_of_threshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredOuterInner_subcritical_decay_of_threshold_eq
  {d : Nat}
  {q delta beta beta0 : Real}
-- given
  (hq : 1 <= q)
  (hbeta0 : beta <= beta0)
  (hdelta : 0 < delta)
  (hleft : 0 < beta - 2 * delta)
  (hlt : beta < BetaThresholdBound.beta1 (fun b n => IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n b)) :
-- imply
  ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 <= n → wiredOuterInnerTheta d q (beta - 2 * delta) n <= Real.exp (-(((n : Real) / Q) * delta)) := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredOuterInner_subcritical_decay_of_threshold d q delta beta beta0 hq hbeta0 hdelta hleft hlt

/--
[wiredOuterInnerTheta_eq_wiredFiniteMeasure_double](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredOuterInnerTheta_eq_wiredFiniteMeasure_double_eq
  {d n : Nat}
  {beta : Real}
-- given
  (hn : 1 <= n)
  (hbeta : 0 < beta) :
-- imply
  wiredOuterInnerTheta d 2 beta n = (FK.wiredFiniteMeasure d (2 * n) (by have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0) linarith : 0 < 1 - Real.exp (-beta)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (by norm_num : (0 : Real) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (FK.boxBdryConnEvent d n) := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredOuterInnerTheta_eq_wiredFiniteMeasure_double d n hn beta hbeta

/--
[wiredOuterInnerTheta_tendsto_fkTheta_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredOuterInnerTheta_tendsto_fkTheta_q2_eq
  {d : Nat}
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  Filter.Tendsto (fun n => wiredOuterInnerTheta d 2 beta n) Filter.atTop (nhds (FK.fkTheta d (by have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0) linarith : 0 < 1 - Real.exp (-beta)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (by norm_num : (0 : Real) < 2) (q := 2))) := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredOuterInnerTheta_tendsto_fkTheta_q2 d beta hbeta

/--
[wiredThresholdTheta_tendsto_fkTheta_div_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredThresholdTheta_tendsto_fkTheta_div_q2_eq
  {d : Nat}
  {beta0 beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  Filter.Tendsto (fun n => wiredThresholdTheta d 2 beta0 n beta) Filter.atTop (nhds (FK.fkTheta d (by have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0) linarith : 0 < 1 - Real.exp (-beta)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (by norm_num : (0 : Real) < 2) (q := 2) / wiredSharpConstant d beta0)) := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredThresholdTheta_tendsto_fkTheta_div_q2 d beta0 beta hbeta

/--
[wiredThresholdSet_mem_of_fkTheta_pos_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredThresholdSet_mem_of_fkTheta_pos_q2_eq
  {d : Nat}
  {beta0 beta : Real}
-- given
  (hbeta : 0 < beta)
  (hTheta : 0 < FK.fkTheta d (by have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0) linarith : 0 < 1 - Real.exp (-beta)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (by norm_num : (0 : Real) < 2) (q := 2)) :
-- imply
  beta ∈ BetaThresholdBound.thresholdSet (fun b n => IntegrationSubcritical.Sig (wiredThresholdTheta d 2 beta0) n b) := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredThresholdSet_mem_of_fkTheta_pos_q2 d beta0 beta hbeta hTheta

/--
[wiredThresholdSet_nonempty_of_fkTheta_pos_q2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean)
-/
@[path]
private lemma wiredThresholdSet_nonempty_of_fkTheta_pos_q2_eq
  {d : Nat}
  {beta0 beta : Real}
-- given
  (hbeta : 0 < beta)
  (hTheta : 0 < FK.fkTheta d (by have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0) linarith : 0 < 1 - Real.exp (-beta)) (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1) (by norm_num : (0 : Real) < 2) (q := 2)) :
-- imply
  (BetaThresholdBound.thresholdSet (fun b n => IntegrationSubcritical.Sig (wiredThresholdTheta d 2 beta0) n b)).Nonempty := by
-- proof
  apply StatMech.OSSS.WiredBoxSharpness.wiredThresholdSet_nonempty_of_fkTheta_pos_q2 d beta0 beta hbeta hTheta


-- created on 2026-10-23
