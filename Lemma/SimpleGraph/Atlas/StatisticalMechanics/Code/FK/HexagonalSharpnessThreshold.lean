import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpnessThreshold
open Finset Set Filter Topology MeasureTheory StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[hexagonalSharpConstant_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hexagonalSharpConstant_le_one_eq
  {beta0 : Real}
-- given
  (hbeta0 : 0 <= beta0) :
-- imply
  hexagonalSharpConstant beta0 <= 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalSharpConstant_le_one beta0 hbeta0

/--
[one_le_inv_hexagonalSharpConstant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma one_le_inv_hexagonalSharpConstant_eq
  {beta0 : Real}
-- given
  (hbeta0 : 0 <= beta0) :
-- imply
  1 <= 1 / hexagonalSharpConstant beta0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.one_le_inv_hexagonalSharpConstant beta0 hbeta0

/--
[hexagonalOuterInnerTheta_eq_activeBCMean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hexagonalOuterInnerTheta_eq_activeBCMean_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 <= n) :
-- imply
  hexagonalOuterInnerTheta q beta n = FK.activeBCMean (hexagonalBoxGraph (2 * n)) (hexagonalBoxBoundaryGraph (2 * n)) (FK.betaParams (fun _ => 1) beta) q (hexagonalInnerCrossInd n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalOuterInnerTheta_eq_activeBCMean n hn q beta

/--
[hasDerivAt_hexagonalOuterInnerTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hasDerivAt_hexagonalOuterInnerTheta_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  HasDerivAt (fun b => hexagonalOuterInnerTheta q b n) (hexagonalOuterInnerThetaPrime n q beta) beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hasDerivAt_hexagonalOuterInnerTheta n hn q beta hq hbeta

/--
[hexagonalNormalizedSig_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hexagonalNormalizedSig_eq_eq
  {n : Nat}
  {q beta0 beta : Real} :
-- imply
  IntegrationSubcritical.Sig (hexagonalNormalizedTheta q beta0) n beta = hexagonalOuterInnerSig n q beta / hexagonalSharpConstant beta0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalNormalizedSig_eq n q beta0 beta

/--
[hexagonalNormalizedTheta_differential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hexagonalNormalizedTheta_differential_eq
  {n : Nat}
  {q beta beta0 : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hbeta0 : beta <= beta0) :
-- imply
  (((n : Real) / IntegrationSubcritical.Sig (hexagonalNormalizedTheta q beta0) n beta) * hexagonalNormalizedTheta q beta0 n beta) <= hexagonalNormalizedThetaPrime q beta0 n beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalNormalizedTheta_differential n hn q beta beta0 hq hbeta hbeta0

/--
[hasDerivAt_hexagonalNormalizedTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hasDerivAt_hexagonalNormalizedTheta_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  HasDerivAt (hexagonalNormalizedTheta q beta0 n) (hexagonalNormalizedThetaPrime q beta0 n beta) beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hasDerivAt_hexagonalNormalizedTheta n hn q beta0 beta hq hbeta

/--
[hexagonalOuterInnerTheta_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hexagonalOuterInnerTheta_le_one_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  hexagonalOuterInnerTheta q beta n <= 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalOuterInnerTheta_le_one n q beta hq hbeta

/--
[hexagonalNormalizedTheta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hexagonalNormalizedTheta_nonneg_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 <= hexagonalNormalizedTheta q beta0 n beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalNormalizedTheta_nonneg n q beta0 beta hq hbeta

/--
[hexagonalNormalizedTheta_le_invConstant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hexagonalNormalizedTheta_le_invConstant_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  hexagonalNormalizedTheta q beta0 n beta <= 1 / hexagonalSharpConstant beta0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalNormalizedTheta_le_invConstant n q beta0 beta hq hbeta

/--
[hexagonalNormalizedSig_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hexagonalNormalizedSig_pos_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 < IntegrationSubcritical.Sig (hexagonalNormalizedTheta q beta0) n beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalNormalizedSig_pos n hn q beta0 beta hq hbeta

/--
[hexagonalOuterInnerThetaPrime_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hexagonalOuterInnerThetaPrime_nonneg_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 <= hexagonalOuterInnerThetaPrime n q beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalOuterInnerThetaPrime_nonneg n hn q beta hq hbeta

/--
[hexagonalNormalizedThetaPrime_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hexagonalNormalizedThetaPrime_nonneg_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 <= hexagonalNormalizedThetaPrime q beta0 n beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalNormalizedThetaPrime_nonneg n hn q beta0 beta hq hbeta

/--
[hexagonalNormalizedTheta_mono_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hexagonalNormalizedTheta_mono_beta_eq
  {n : Nat}
  {q beta0 y x : Real}
-- given
  (hq : 1 <= q)
  (hy : 0 < y)
  (hyx : y <= x) :
-- imply
  hexagonalNormalizedTheta q beta0 n y <= hexagonalNormalizedTheta q beta0 n x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalNormalizedTheta_mono_beta n q beta0 y x hq hy hyx

/--
[hexagonalThresholdTheta_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hexagonalThresholdTheta_of_pos_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  hexagonalThresholdTheta q beta0 n beta = hexagonalNormalizedTheta q beta0 n beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalThresholdTheta_of_pos n q beta0 beta hbeta

/--
[hexagonalThresholdSig_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hexagonalThresholdSig_of_pos_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  IntegrationSubcritical.Sig (hexagonalThresholdTheta q beta0) n beta = IntegrationSubcritical.Sig (hexagonalNormalizedTheta q beta0) n beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalThresholdSig_of_pos n q beta0 beta hbeta

/--
[hexagonalThresholdSig_of_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hexagonalThresholdSig_of_nonpos_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hn : 1 <= n)
  (hbeta : beta <= 0) :
-- imply
  IntegrationSubcritical.Sig (hexagonalThresholdTheta q beta0) n beta = 1 / hexagonalSharpConstant beta0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalThresholdSig_of_nonpos n hn q beta0 beta hbeta

/--
[hexagonalThresholdSet_bddBelow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hexagonalThresholdSet_bddBelow_eq
  {q beta0 : Real} :
-- imply
  BddBelow (BetaThresholdBound.thresholdSet (fun b n => IntegrationSubcritical.Sig (hexagonalThresholdTheta q beta0) n b)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalThresholdSet_bddBelow q beta0

/--
[hexagonalThresholdTheta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hexagonalThresholdTheta_nonneg_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hq : 1 <= q) :
-- imply
  0 <= hexagonalThresholdTheta q beta0 n beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalThresholdTheta_nonneg n q beta0 beta hq

/--
[hexagonalThresholdTheta_le_invConstant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hexagonalThresholdTheta_le_invConstant_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hq : 1 <= q) :
-- imply
  hexagonalThresholdTheta q beta0 n beta <= 1 / hexagonalSharpConstant beta0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalThresholdTheta_le_invConstant n q beta0 beta hq

/--
[hexagonalThresholdTheta_mono_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hexagonalThresholdTheta_mono_beta_eq
  {n : Nat}
  {q beta0 a b : Real}
-- given
  (hq : 1 <= q)
  (hab : a <= b) :
-- imply
  hexagonalThresholdTheta q beta0 n a <= hexagonalThresholdTheta q beta0 n b := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalThresholdTheta_mono_beta n q beta0 a b hq hab

/--
[hexagonalThresholdSig_mono_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hexagonalThresholdSig_mono_beta_eq
  {n : Nat}
  {q beta0 : Real}
  {a b : Real}
-- given
  (hq : 1 <= q)
  (hab : a <= b) :
-- imply
  IntegrationSubcritical.Sig (hexagonalThresholdTheta q beta0) n a <= IntegrationSubcritical.Sig (hexagonalThresholdTheta q beta0) n b := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalThresholdSig_mono_beta n q beta0 hq hab

/--
[hexagonalThresholdSig_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hexagonalThresholdSig_pos_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q) :
-- imply
  0 < IntegrationSubcritical.Sig (hexagonalThresholdTheta q beta0) n beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalThresholdSig_pos n hn q beta0 beta hq

/--
[hexagonalThresholdSig_le_linear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hexagonalThresholdSig_le_linear_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hq : 1 <= q) :
-- imply
  IntegrationSubcritical.Sig (hexagonalThresholdTheta q beta0) n beta <= (1 / hexagonalSharpConstant beta0) * (n : Real) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalThresholdSig_le_linear n q beta0 beta hq

/--
[hexagonalOuterInner_subcritical_decay_of_threshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessThreshold.lean)
-/
@[path]
private lemma hexagonalOuterInner_subcritical_decay_of_threshold_eq
  {q delta beta beta0 : Real}
-- given
  (hq : 1 <= q)
  (hbeta0 : beta <= beta0)
  (hdelta : 0 < delta)
  (hleft : 0 < beta - 2 * delta)
  (hlt : beta < BetaThresholdBound.beta1 (fun b n => IntegrationSubcritical.Sig (hexagonalThresholdTheta q beta0) n b)) :
-- imply
  ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 <= n → hexagonalOuterInnerTheta q (beta - 2 * delta) n <= Real.exp (-(((n : Real) / Q) * delta)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalOuterInner_subcritical_decay_of_threshold q delta beta beta0 hq hbeta0 hdelta hleft hlt


-- created on 2026-10-23
