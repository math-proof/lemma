import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackage.Part7
open StatMech StatMech.Exact3D StatMech.Exact3D.InfiniteTailWitnessPackage


/--
[rgMap_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma rgMap_scale_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  W.rgMap.scale = W.scale := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgMap_scale W

/--
[fixedPoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma fixedPoint_eq_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  W.rgMap.map W.fixedPoint = W.fixedPoint := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.fixedPoint_eq W

/--
[certificate_scale_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma certificate_scale_eq_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  W.certificate.scale = W.scale := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.certificate_scale_eq W

/--
[certificate_thermalEigenvalue_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma certificate_thermalEigenvalue_eq_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  W.certificate.thermalEigenvalue = W.thermal := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.certificate_thermalEigenvalue_eq W

/--
[certificate_fixedPoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma certificate_fixedPoint_eq_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  W.certificate.fixedPointData.fixedPoint = W.fixedPoint := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.certificate_fixedPoint_eq W

/--
[certificate_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma certificate_predictedExponent_eq_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  W.certificate.predictedExponent = predictedNu W.scale W.thermal := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.certificate_predictedExponent_eq W

/--
[retarget_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma retarget_certificate_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  (W.retarget N).certificate = W.certificate.retarget N := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.retarget_certificate W N

/--
[ofFiniteWitnessPackage_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma ofFiniteWitnessPackage_certificate_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  (ofFiniteWitnessPackage W).certificate = W.certificate := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.ofFiniteWitnessPackage_certificate W

/--
[ofFiniteWitnessPackage_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma ofFiniteWitnessPackage_rgToExponentBridge_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength) :
-- imply
  (ofFiniteWitnessPackage W).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.ofFiniteWitnessPackage_rgToExponentBridge W hbridge

/--
[ofFiniteWitnessPackage_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma ofFiniteWitnessPackage_valid_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hvalid : W.certificate.Valid correlationLength) :
-- imply
  (ofFiniteWitnessPackage W).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.ofFiniteWitnessPackage_valid W hvalid

/--
[ofFiniteWitnessPackage_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma ofFiniteWitnessPackage_hasCriticalNu_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hν : HasCriticalNu M correlationLength W.certificate.predictedExponent) :
-- imply
  HasCriticalNu M correlationLength (ofFiniteWitnessPackage W).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.ofFiniteWitnessPackage_hasCriticalNu W hν

/--
[ofFiniteWitnessPackage_retarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma ofFiniteWitnessPackage_retarget_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  (ofFiniteWitnessPackage W).retarget N = ofFiniteWitnessPackage (W.retarget N) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.ofFiniteWitnessPackage_retarget W N

/--
[retarget_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma retarget_rgToExponentBridge_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength)
  (hβc : M.betaC = N.betaC) :
-- imply
  (W.retarget N).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.retarget_rgToExponentBridge W N hbridge hβc

/--
[retarget_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma retarget_valid_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hvalid : W.certificate.Valid correlationLength)
  (hβc : M.betaC = N.betaC) :
-- imply
  (W.retarget N).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.retarget_valid W N hvalid hβc

/--
[retarget_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma retarget_hasCriticalNu_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hν : HasCriticalNu M correlationLength W.certificate.predictedExponent)
  (hβc : M.betaC = N.betaC) :
-- imply
  HasCriticalNu N correlationLength ((W.retarget N).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.retarget_hasCriticalNu W N hν hβc

/--
[retarget_rgToExponentBridge_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma retarget_rgToExponentBridge_iff_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hβc : M.betaC = N.betaC) :
-- imply
  W.certificate.RGToExponentBridge correlationLength ↔ (W.retarget N).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.retarget_rgToExponentBridge_iff W N hβc

/--
[retarget_valid_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma retarget_valid_iff_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hβc : M.betaC = N.betaC) :
-- imply
  W.certificate.Valid correlationLength ↔ (W.retarget N).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.retarget_valid_iff W N hβc

/--
[retarget_hasCriticalNu_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma retarget_hasCriticalNu_iff_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hβc : M.betaC = N.betaC) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent ↔ HasCriticalNu N correlationLength ((W.retarget N).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.retarget_hasCriticalNu_iff W N hβc

/--
[fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma fixedPointEnclosure_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  W.certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.fixedPointEnclosure W

/--
[finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma finiteChecks_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  W.certificate.FiniteChecks where finiteCaseChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.finiteChecks W

/--
[finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma finiteCaseChecks_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  W.certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.finiteCaseChecks W

/--
[tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma tailBounds_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  W.certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.tailBounds W

/--
[linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma linearizationEnclosure_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  W.certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.linearizationEnclosure W

/--
[hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma hyperbolicSplitting_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  W.certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hyperbolicSplitting W

/--
[orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma orbitEntry_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  W.certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.orbitEntry W

/--
[summable_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma summable_tailContribution_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  Summable W.tailContribution := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.summable_tailContribution W

/--
[summable_tailWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma summable_tailWeight_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  Summable W.tailCertificate.tailWeight := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.summable_tailWeight W

/--
[retarget_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma retarget_tailPrefixSum_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  (W.retarget N).tailPrefixSum = W.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.retarget_tailPrefixSum W N

/--
[retarget_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma retarget_tailBudget_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  (W.retarget N).tailBudget = W.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.retarget_tailBudget W N

/--
[retarget_tailCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma retarget_tailCertifiedTotalBound_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  (W.retarget N).tailCertifiedTotalBound = W.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.retarget_tailCertifiedTotalBound W N

/--
[retarget_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma retarget_tailContribution_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  (W.retarget N).tailContribution = W.tailContribution := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.retarget_tailContribution W N

/--
[retarget_tailTotalTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma retarget_tailTotalTsum_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  (W.retarget N).tailTotalTsum = W.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.retarget_tailTotalTsum W N

/--
[retarget_tailRemainderSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma retarget_tailRemainderSum_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  (W.retarget N).tailRemainderSum = W.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.retarget_tailRemainderSum W N

/--
[retarget_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma retarget_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  (W.retarget N).certificate.predictedExponent = W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.retarget_predictedExponent W N

/--
[tailTotalTsum_eq_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_eq_tsum_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  W.tailTotalTsum = ∑' a, W.tailCertificate.weight a := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.tailTotalTsum_eq_tsum W

/--
[tailContribution_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma tailContribution_nonneg_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {a : α}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  0 ≤ W.tailContribution a := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.tailContribution_nonneg W a

/--
[tailContribution_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma tailContribution_decomposition_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {a : α}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  W.tailContribution a = W.tailCertificate.prefixWeight a + W.tailCertificate.tailWeight a := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.tailContribution_decomposition W a

/--
[tailTotalTsum_eq_prefix_add_remainder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_eq_prefix_add_remainder_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  W.tailTotalTsum = W.tailPrefixSum + W.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.tailTotalTsum_eq_prefix_add_remainder W

/--
[tailRemainderSum_le_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma tailRemainderSum_le_tailBudget_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  W.tailRemainderSum ≤ W.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.tailRemainderSum_le_tailBudget W

/--
[tailRemainderSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma tailRemainderSum_nonneg_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  0 ≤ W.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.tailRemainderSum_nonneg W

/--
[tailRemainderSum_eq_zero_of_tailBudget_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma tailRemainderSum_eq_zero_of_tailBudget_eq_zero_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hbudget : W.tailBudget = 0) :
-- imply
  W.tailRemainderSum = 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.tailRemainderSum_eq_zero_of_tailBudget_eq_zero W hbudget

/--
[tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hbudget : W.tailBudget = 0) :
-- imply
  W.tailTotalTsum = W.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero W hbudget

/--
[tail_tsum_le_prefix_add_tailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma tail_tsum_le_prefix_add_tailBound_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  (∑' a, W.tailCertificate.weight a) ≤ W.tailCertificate.prefixSum + W.tailCertificate.tailBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.tail_tsum_le_prefix_add_tailBound W

/--
[tail_tsum_le_certifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma tail_tsum_le_certifiedTotalBound_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  (∑' a, W.tailCertificate.weight a) ≤ W.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.tail_tsum_le_certifiedTotalBound W

/--
[tail_tsum_le_of_certifiedTotalBound_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma tail_tsum_le_of_certifiedTotalBound_le_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {B : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hB : W.tailCertifiedTotalBound ≤ B) :
-- imply
  (∑' a, W.tailCertificate.weight a) ≤ B := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.tail_tsum_le_of_certifiedTotalBound_le W hB

/--
[tailTotalTsum_le_certifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_le_certifiedTotalBound_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  W.tailTotalTsum ≤ W.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.tailTotalTsum_le_certifiedTotalBound W

/--
[tailTotalTsum_le_of_certifiedTotalBound_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_le_of_certifiedTotalBound_le_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {B : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hB : W.tailCertifiedTotalBound ≤ B) :
-- imply
  W.tailTotalTsum ≤ B := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.tailTotalTsum_le_of_certifiedTotalBound_le W hB

/--
[tail_tsum_le_prefix_add_of_tailBudget_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma tail_tsum_le_prefix_add_of_tailBudget_le_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  (∑' a, W.tailCertificate.weight a) ≤ W.tailPrefixSum + tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.tail_tsum_le_prefix_add_of_tailBudget_le W hle

/--
[tailTotalTsum_le_prefix_add_of_tailBudget_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_le_prefix_add_of_tailBudget_le_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  W.tailTotalTsum ≤ W.tailPrefixSum + tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.tailTotalTsum_le_prefix_add_of_tailBudget_le W hle

/--
[tailRemainderSum_le_of_tailBudget_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma tailRemainderSum_le_of_tailBudget_le_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  W.tailRemainderSum ≤ tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.tailRemainderSum_le_of_tailBudget_le W hle

/--
[tailCertifiedTotalBound_le_prefix_add_of_tailBudget_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma tailCertifiedTotalBound_le_prefix_add_of_tailBudget_le_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  W.tailCertifiedTotalBound ≤ W.tailPrefixSum + tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.tailCertifiedTotalBound_le_prefix_add_of_tailBudget_le W hle

/--
[ofFiniteWitnessPackage_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma ofFiniteWitnessPackage_tailPrefixSum_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  (ofFiniteWitnessPackage W).tailPrefixSum = W.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.ofFiniteWitnessPackage_tailPrefixSum W

/--
[ofFiniteWitnessPackage_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma ofFiniteWitnessPackage_tailBudget_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  (ofFiniteWitnessPackage W).tailBudget = W.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.ofFiniteWitnessPackage_tailBudget W

/--
[ofFiniteWitnessPackage_tailCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma ofFiniteWitnessPackage_tailCertifiedTotalBound_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  (ofFiniteWitnessPackage W).tailCertifiedTotalBound = W.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.ofFiniteWitnessPackage_tailCertifiedTotalBound W

/--
[ofFiniteWitnessPackage_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma ofFiniteWitnessPackage_tailContribution_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  (ofFiniteWitnessPackage W).tailContribution = W.tailContribution := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.ofFiniteWitnessPackage_tailContribution W

/--
[ofFiniteWitnessPackage_tailTotalTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma ofFiniteWitnessPackage_tailTotalTsum_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  (ofFiniteWitnessPackage W).tailTotalTsum = W.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.ofFiniteWitnessPackage_tailTotalTsum W

/--
[ofFiniteWitnessPackage_tailRemainderSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma ofFiniteWitnessPackage_tailRemainderSum_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  (ofFiniteWitnessPackage W).tailRemainderSum = W.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.ofFiniteWitnessPackage_tailRemainderSum W

/--
[tailPrefixSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma tailPrefixSum_nonneg_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  0 ≤ W.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.tailPrefixSum_nonneg W

/--
[tailBudget_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma tailBudget_nonneg_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  0 ≤ W.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.tailBudget_nonneg W

/--
[tailCertifiedTotalBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma tailCertifiedTotalBound_nonneg_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  0 ≤ W.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.tailCertifiedTotalBound_nonneg W

/--
[tail_tsum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma tail_tsum_nonneg_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  0 ≤ ∑' a, W.tailCertificate.weight a := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.tail_tsum_nonneg W

/--
[tailTotalTsum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_nonneg_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  0 ≤ W.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.tailTotalTsum_nonneg W

/--
[with_larger_tailBudget_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBudget_tailBudget_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  (W.with_larger_tailBudget hle).tailBudget = tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.with_larger_tailBudget_tailBudget W hle

/--
[with_larger_tailBudget_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBudget_tailPrefixSum_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  (W.with_larger_tailBudget hle).tailPrefixSum = W.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.with_larger_tailBudget_tailPrefixSum W hle

/--
[with_larger_tailBudget_tailCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBudget_tailCertifiedTotalBound_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  (W.with_larger_tailBudget hle).tailCertifiedTotalBound = W.tailPrefixSum + tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.with_larger_tailBudget_tailCertifiedTotalBound W hle

/--
[with_larger_tailBudget_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBudget_tailContribution_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  (W.with_larger_tailBudget hle).tailContribution = W.tailContribution := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.with_larger_tailBudget_tailContribution W hle

/--
[with_larger_tailBudget_tailTotalTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBudget_tailTotalTsum_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  (W.with_larger_tailBudget hle).tailTotalTsum = W.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.with_larger_tailBudget_tailTotalTsum W hle

/--
[with_larger_tailBudget_tailRemainderSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBudget_tailRemainderSum_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  (W.with_larger_tailBudget hle).tailRemainderSum = W.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.with_larger_tailBudget_tailRemainderSum W hle

/--
[with_larger_tailBudget_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBudget_certificate_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  (W.with_larger_tailBudget hle).certificate = W.certificate := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.with_larger_tailBudget_certificate W hle

/--
[with_larger_tailBudget_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBudget_rgToExponentBridge_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound')
  (hbridge : W.certificate.RGToExponentBridge correlationLength) :
-- imply
  (W.with_larger_tailBudget hle).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.with_larger_tailBudget_rgToExponentBridge W hle hbridge

/--
[with_larger_tailBudget_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBudget_valid_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound')
  (hvalid : W.certificate.Valid correlationLength) :
-- imply
  (W.with_larger_tailBudget hle).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.with_larger_tailBudget_valid W hle hvalid

/--
[with_larger_tailBudget_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBudget_hasCriticalNu_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound')
  (hν : HasCriticalNu M correlationLength W.certificate.predictedExponent) :
-- imply
  HasCriticalNu M correlationLength (W.with_larger_tailBudget hle).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.with_larger_tailBudget_hasCriticalNu W hle hν

/--
[stable_fixedPoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma stable_fixedPoint_mem_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  FiniteContraction.ClosedBall W.stable.contraction.center W.stable.contraction.radius W.stable.fixedPoint := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.stable_fixedPoint_mem W

/--
[stable_exists_unique_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma stable_exists_unique_fixedPoint_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M) :
-- imply
  ∃! p : Fin W.nStable → ℝ, W.stable.map p = p := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.stable_exists_unique_fixedPoint W

/--
[valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma valid_of_bridge_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_bridge W hbridge

/--
[hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma hasCriticalNu_of_bridge_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_bridge W hbridge

/--
[rgToExponentBridge_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma rgToExponentBridge_of_bridge_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_bridge_congr_predictedExponent W hpred hbridge

/--
[valid_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma valid_of_bridge_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_bridge_congr_predictedExponent W hpred hbridge

/--
[hasCriticalNu_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma hasCriticalNu_of_bridge_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.hasCriticalNu_of_bridge_congr_predictedExponent W hpred hbridge

/--
[rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma rgToExponentBridge_of_hasCriticalNu_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hν : HasCriticalNu M correlationLength W.certificate.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.rgToExponentBridge_of_hasCriticalNu W hν

/--
[valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailWitnessPackage.lean)
-/
@[path]
private lemma valid_of_hasCriticalNu_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailWitnessPackage (α := α) M)
  (hν : HasCriticalNu M correlationLength W.certificate.predictedExponent) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailWitnessPackage.valid_of_hasCriticalNu W hν


-- created on 2026-10-23
