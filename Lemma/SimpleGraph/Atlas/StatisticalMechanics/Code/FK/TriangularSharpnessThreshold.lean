import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.TriangularSharpnessThreshold
open Finset Set Filter Topology MeasureTheory StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triangularSharpConstant_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma triangularSharpConstant_le_one_eq
  {beta0 : Real}
-- given
  (hbeta0 : 0 <= beta0) :
-- imply
  triangularSharpConstant beta0 <= 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularSharpConstant_le_one beta0 hbeta0

/--
[one_le_inv_triangularSharpConstant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma one_le_inv_triangularSharpConstant_eq
  {beta0 : Real}
-- given
  (hbeta0 : 0 <= beta0) :
-- imply
  1 <= 1 / triangularSharpConstant beta0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.one_le_inv_triangularSharpConstant beta0 hbeta0

/--
[triangularOuterInnerTheta_eq_activeBCMean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma triangularOuterInnerTheta_eq_activeBCMean_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 <= n) :
-- imply
  triangularOuterInnerTheta q beta n = FK.activeBCMean (triangularBoxGraph (2 * n)) (triangularBoxBoundaryGraph (2 * n)) (FK.betaParams (fun _ => 1) beta) q (triangularInnerCrossInd n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularOuterInnerTheta_eq_activeBCMean n hn q beta

/--
[hasDerivAt_triangularOuterInnerTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma hasDerivAt_triangularOuterInnerTheta_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  HasDerivAt (fun b => triangularOuterInnerTheta q b n) (triangularOuterInnerThetaPrime n q beta) beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hasDerivAt_triangularOuterInnerTheta n hn q beta hq hbeta

/--
[triangularNormalizedSig_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma triangularNormalizedSig_eq_eq
  {n : Nat}
  {q beta0 beta : Real} :
-- imply
  IntegrationSubcritical.Sig (triangularNormalizedTheta q beta0) n beta = triangularOuterInnerSig n q beta / triangularSharpConstant beta0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularNormalizedSig_eq n q beta0 beta

/--
[triangularNormalizedTheta_differential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma triangularNormalizedTheta_differential_eq
  {n : Nat}
  {q beta beta0 : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hbeta0 : beta <= beta0) :
-- imply
  (((n : Real) / IntegrationSubcritical.Sig (triangularNormalizedTheta q beta0) n beta) * triangularNormalizedTheta q beta0 n beta) <= triangularNormalizedThetaPrime q beta0 n beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularNormalizedTheta_differential n hn q beta beta0 hq hbeta hbeta0

/--
[hasDerivAt_triangularNormalizedTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma hasDerivAt_triangularNormalizedTheta_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  HasDerivAt (triangularNormalizedTheta q beta0 n) (triangularNormalizedThetaPrime q beta0 n beta) beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hasDerivAt_triangularNormalizedTheta n hn q beta0 beta hq hbeta

/--
[triangularOuterInnerTheta_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma triangularOuterInnerTheta_le_one_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  triangularOuterInnerTheta q beta n <= 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularOuterInnerTheta_le_one n q beta hq hbeta

/--
[triangularNormalizedTheta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma triangularNormalizedTheta_nonneg_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 <= triangularNormalizedTheta q beta0 n beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularNormalizedTheta_nonneg n q beta0 beta hq hbeta

/--
[triangularNormalizedTheta_le_invConstant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma triangularNormalizedTheta_le_invConstant_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  triangularNormalizedTheta q beta0 n beta <= 1 / triangularSharpConstant beta0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularNormalizedTheta_le_invConstant n q beta0 beta hq hbeta

/--
[triangularNormalizedSig_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma triangularNormalizedSig_pos_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 < IntegrationSubcritical.Sig (triangularNormalizedTheta q beta0) n beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularNormalizedSig_pos n hn q beta0 beta hq hbeta

/--
[triangularOuterInnerThetaPrime_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma triangularOuterInnerThetaPrime_nonneg_eq
  {n : Nat}
  {q beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 <= triangularOuterInnerThetaPrime n q beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularOuterInnerThetaPrime_nonneg n hn q beta hq hbeta

/--
[triangularNormalizedThetaPrime_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma triangularNormalizedThetaPrime_nonneg_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  0 <= triangularNormalizedThetaPrime q beta0 n beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularNormalizedThetaPrime_nonneg n hn q beta0 beta hq hbeta

/--
[triangularNormalizedTheta_mono_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma triangularNormalizedTheta_mono_beta_eq
  {n : Nat}
  {q beta0 y x : Real}
-- given
  (hq : 1 <= q)
  (hy : 0 < y)
  (hyx : y <= x) :
-- imply
  triangularNormalizedTheta q beta0 n y <= triangularNormalizedTheta q beta0 n x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularNormalizedTheta_mono_beta n q beta0 y x hq hy hyx

/--
[triangularThresholdTheta_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma triangularThresholdTheta_of_pos_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  triangularThresholdTheta q beta0 n beta = triangularNormalizedTheta q beta0 n beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularThresholdTheta_of_pos n q beta0 beta hbeta

/--
[triangularThresholdSig_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma triangularThresholdSig_of_pos_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  IntegrationSubcritical.Sig (triangularThresholdTheta q beta0) n beta = IntegrationSubcritical.Sig (triangularNormalizedTheta q beta0) n beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularThresholdSig_of_pos n q beta0 beta hbeta

/--
[triangularThresholdSig_of_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma triangularThresholdSig_of_nonpos_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hn : 1 <= n)
  (hbeta : beta <= 0) :
-- imply
  IntegrationSubcritical.Sig (triangularThresholdTheta q beta0) n beta = 1 / triangularSharpConstant beta0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularThresholdSig_of_nonpos n hn q beta0 beta hbeta

/--
[triangularThresholdSet_bddBelow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma triangularThresholdSet_bddBelow_eq
  {q beta0 : Real} :
-- imply
  BddBelow (BetaThresholdBound.thresholdSet (fun b n => IntegrationSubcritical.Sig (triangularThresholdTheta q beta0) n b)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularThresholdSet_bddBelow q beta0

/--
[triangularThresholdTheta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma triangularThresholdTheta_nonneg_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hq : 1 <= q) :
-- imply
  0 <= triangularThresholdTheta q beta0 n beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularThresholdTheta_nonneg n q beta0 beta hq

/--
[triangularThresholdTheta_le_invConstant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma triangularThresholdTheta_le_invConstant_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hq : 1 <= q) :
-- imply
  triangularThresholdTheta q beta0 n beta <= 1 / triangularSharpConstant beta0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularThresholdTheta_le_invConstant n q beta0 beta hq

/--
[triangularThresholdTheta_mono_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma triangularThresholdTheta_mono_beta_eq
  {n : Nat}
  {q beta0 a b : Real}
-- given
  (hq : 1 <= q)
  (hab : a <= b) :
-- imply
  triangularThresholdTheta q beta0 n a <= triangularThresholdTheta q beta0 n b := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularThresholdTheta_mono_beta n q beta0 a b hq hab

/--
[triangularThresholdSig_mono_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma triangularThresholdSig_mono_beta_eq
  {n : Nat}
  {q beta0 : Real}
  {a b : Real}
-- given
  (hq : 1 <= q)
  (hab : a <= b) :
-- imply
  IntegrationSubcritical.Sig (triangularThresholdTheta q beta0) n a <= IntegrationSubcritical.Sig (triangularThresholdTheta q beta0) n b := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularThresholdSig_mono_beta n q beta0 hq hab

/--
[triangularThresholdSig_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma triangularThresholdSig_pos_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q) :
-- imply
  0 < IntegrationSubcritical.Sig (triangularThresholdTheta q beta0) n beta := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularThresholdSig_pos n hn q beta0 beta hq

/--
[triangularThresholdSig_le_linear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma triangularThresholdSig_le_linear_eq
  {n : Nat}
  {q beta0 beta : Real}
-- given
  (hq : 1 <= q) :
-- imply
  IntegrationSubcritical.Sig (triangularThresholdTheta q beta0) n beta <= (1 / triangularSharpConstant beta0) * (n : Real) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularThresholdSig_le_linear n q beta0 beta hq

/--
[triangularOuterInner_subcritical_decay_of_threshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessThreshold.lean)
-/
@[path]
private lemma triangularOuterInner_subcritical_decay_of_threshold_eq
  {q delta beta beta0 : Real}
-- given
  (hq : 1 <= q)
  (hbeta0 : beta <= beta0)
  (hdelta : 0 < delta)
  (hleft : 0 < beta - 2 * delta)
  (hlt : beta < BetaThresholdBound.beta1 (fun b n => IntegrationSubcritical.Sig (triangularThresholdTheta q beta0) n b)) :
-- imply
  ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 <= n → triangularOuterInnerTheta q (beta - 2 * delta) n <= Real.exp (-(((n : Real) / Q) * delta)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularOuterInner_subcritical_decay_of_threshold q delta beta beta0 hq hbeta0 hdelta hleft hlt


-- created on 2026-10-23
