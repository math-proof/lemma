import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailMaskedTableWitnessPackage.Part9
open StatMech StatMech.Exact3D StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage


/--
[retarget_toWitnessPackage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma retarget_toWitnessPackage_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  (W.retarget N).toWitnessPackage = W.toWitnessPackage.retarget N := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.retarget_toWitnessPackage W N

/--
[certificate_scale_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma certificate_scale_eq_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  W.certificate.scale = W.scale := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.certificate_scale_eq W

/--
[certificate_thermalEigenvalue_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma certificate_thermalEigenvalue_eq_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  W.certificate.thermalEigenvalue = W.thermal := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.certificate_thermalEigenvalue_eq W

/--
[certificate_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma certificate_predictedExponent_eq_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  W.certificate.predictedExponent = predictedNu W.scale W.thermal := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.certificate_predictedExponent_eq W

/--
[retarget_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma retarget_certificate_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  (W.retarget N).certificate = W.certificate.retarget N := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.retarget_certificate W N

/--
[retarget_finiteBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma retarget_finiteBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  (W.retarget N).finiteBound = W.finiteBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.retarget_finiteBound W N

/--
[retarget_prefixTailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma retarget_prefixTailBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  (W.retarget N).prefixTailBound = W.prefixTailBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.retarget_prefixTailBound W N

/--
[retarget_tailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma retarget_tailBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  (W.retarget N).tailBound = W.tailBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.retarget_tailBound W N

/--
[retarget_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma retarget_rgToExponentBridge_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength)
  (hβc : M.betaC = N.betaC) :
-- imply
  (W.retarget N).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.retarget_rgToExponentBridge W N hbridge hβc

/--
[retarget_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma retarget_valid_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hvalid : W.certificate.Valid correlationLength)
  (hβc : M.betaC = N.betaC) :
-- imply
  (W.retarget N).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.retarget_valid W N hvalid hβc

/--
[retarget_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma retarget_hasCriticalNu_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hν : HasCriticalNu M correlationLength W.certificate.predictedExponent)
  (hβc : M.betaC = N.betaC) :
-- imply
  HasCriticalNu N correlationLength ((W.retarget N).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.retarget_hasCriticalNu W N hν hβc

/--
[retarget_rgToExponentBridge_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma retarget_rgToExponentBridge_iff_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hβc : M.betaC = N.betaC) :
-- imply
  W.certificate.RGToExponentBridge correlationLength ↔ (W.retarget N).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.retarget_rgToExponentBridge_iff W N hβc

/--
[retarget_valid_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma retarget_valid_iff_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hβc : M.betaC = N.betaC) :
-- imply
  W.certificate.Valid correlationLength ↔ (W.retarget N).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.retarget_valid_iff W N hβc

/--
[retarget_hasCriticalNu_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma retarget_hasCriticalNu_iff_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hβc : M.betaC = N.betaC) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent ↔ HasCriticalNu N correlationLength ((W.retarget N).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.retarget_hasCriticalNu_iff W N hβc

/--
[finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma finiteChecks_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  W.certificate.FiniteChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.finiteChecks W

/--
[finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma finiteCaseChecks_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  W.certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.finiteCaseChecks W

/--
[tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailBounds_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  W.certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailBounds W

/--
[fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma fixedPointEnclosure_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  W.certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.fixedPointEnclosure W

/--
[linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma linearizationEnclosure_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  W.certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.linearizationEnclosure W

/--
[hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma hyperbolicSplitting_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  W.certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.hyperbolicSplitting W

/--
[orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma orbitEntry_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  W.certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.orbitEntry W

/--
[tailBudget_eq_tailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailBudget_eq_tailBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  W.tailBudget = W.tailBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailBudget_eq_tailBound W

/--
[retarget_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma retarget_tailPrefixSum_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  (W.retarget N).tailPrefixSum = W.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.retarget_tailPrefixSum W N

/--
[retarget_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma retarget_tailBudget_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  (W.retarget N).tailBudget = W.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.retarget_tailBudget W N

/--
[retarget_tailCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma retarget_tailCertifiedTotalBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  (W.retarget N).tailCertifiedTotalBound = W.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.retarget_tailCertifiedTotalBound W N

/--
[retarget_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma retarget_tailContribution_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  (W.retarget N).tailContribution = W.tailContribution := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.retarget_tailContribution W N

/--
[retarget_tailTotalTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma retarget_tailTotalTsum_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  (W.retarget N).tailTotalTsum = W.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.retarget_tailTotalTsum W N

/--
[retarget_tailRemainderSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma retarget_tailRemainderSum_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  (W.retarget N).tailRemainderSum = W.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.retarget_tailRemainderSum W N

/--
[retarget_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma retarget_predictedExponent_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  (W.retarget N).certificate.predictedExponent = W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.retarget_predictedExponent W N

/--
[summable_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma summable_tailContribution_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  Summable W.tailContribution := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.summable_tailContribution W

/--
[tailContribution_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailContribution_nonneg_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {a : α}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  0 ≤ W.tailContribution a := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailContribution_nonneg W a

/--
[tailPrefixSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailPrefixSum_nonneg_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  0 ≤ W.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailPrefixSum_nonneg W

/--
[tailBudget_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailBudget_nonneg_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  0 ≤ W.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailBudget_nonneg W

/--
[tailCertifiedTotalBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailCertifiedTotalBound_nonneg_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  0 ≤ W.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailCertifiedTotalBound_nonneg W

/--
[tailTotalTsum_eq_tsum_totalContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_eq_tsum_totalContribution_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  W.tailTotalTsum = ∑' a, W.S.totalContribution a := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailTotalTsum_eq_tsum_totalContribution W

/--
[tailTotalTsum_eq_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_eq_tsum_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  W.tailTotalTsum = ∑' a, W.tailContribution a := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailTotalTsum_eq_tsum W

/--
[tailTotalTsum_eq_prefix_add_remainder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_eq_prefix_add_remainder_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  W.tailTotalTsum = W.tailPrefixSum + W.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailTotalTsum_eq_prefix_add_remainder W

/--
[tail_tsum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tail_tsum_nonneg_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  0 ≤ ∑' a, W.tailContribution a := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tail_tsum_nonneg W

/--
[tailTotalTsum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_nonneg_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  0 ≤ W.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailTotalTsum_nonneg W

/--
[tail_tsum_le_prefix_add_tailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tail_tsum_le_prefix_add_tailBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  (∑' a, W.tailContribution a) ≤ W.tailPrefixSum + W.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tail_tsum_le_prefix_add_tailBound W

/--
[tailRemainderSum_le_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailRemainderSum_le_tailBudget_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  W.tailRemainderSum ≤ W.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailRemainderSum_le_tailBudget W

/--
[tailRemainderSum_le_of_tailBudget_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailRemainderSum_le_of_tailBudget_le_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  W.tailRemainderSum ≤ tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailRemainderSum_le_of_tailBudget_le W hle

/--
[tailRemainderSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailRemainderSum_nonneg_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  0 ≤ W.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailRemainderSum_nonneg W

/--
[tailRemainderSum_eq_zero_of_tailBudget_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailRemainderSum_eq_zero_of_tailBudget_eq_zero_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hbudget : W.tailBudget = 0) :
-- imply
  W.tailRemainderSum = 0 := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailRemainderSum_eq_zero_of_tailBudget_eq_zero W hbudget

/--
[tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hbudget : W.tailBudget = 0) :
-- imply
  W.tailTotalTsum = W.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero W hbudget

/--
[tail_tsum_le_certifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tail_tsum_le_certifiedTotalBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  (∑' a, W.tailContribution a) ≤ W.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tail_tsum_le_certifiedTotalBound W

/--
[tail_tsum_le_of_certifiedTotalBound_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tail_tsum_le_of_certifiedTotalBound_le_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {B : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hB : W.tailCertifiedTotalBound ≤ B) :
-- imply
  (∑' a, W.tailContribution a) ≤ B := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tail_tsum_le_of_certifiedTotalBound_le W hB

/--
[tailTotalTsum_le_certifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_le_certifiedTotalBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  W.tailTotalTsum ≤ W.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailTotalTsum_le_certifiedTotalBound W

/--
[tailTotalTsum_le_of_certifiedTotalBound_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_le_of_certifiedTotalBound_le_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {B : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hB : W.tailCertifiedTotalBound ≤ B) :
-- imply
  W.tailTotalTsum ≤ B := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailTotalTsum_le_of_certifiedTotalBound_le W hB

/--
[tail_tsum_le_prefix_add_of_tailBudget_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tail_tsum_le_prefix_add_of_tailBudget_le_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  (∑' a, W.tailContribution a) ≤ W.tailPrefixSum + tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tail_tsum_le_prefix_add_of_tailBudget_le W hle

/--
[tailTotalTsum_le_prefix_add_of_tailBudget_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_le_prefix_add_of_tailBudget_le_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  W.tailTotalTsum ≤ W.tailPrefixSum + tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailTotalTsum_le_prefix_add_of_tailBudget_le W hle

/--
[tailCertifiedTotalBound_le_prefix_add_of_tailBudget_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailCertifiedTotalBound_le_prefix_add_of_tailBudget_le_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  W.tailCertifiedTotalBound ≤ W.tailPrefixSum + tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailCertifiedTotalBound_le_prefix_add_of_tailBudget_le W hle

/--
[tableCertifiedTotalBound_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tableCertifiedTotalBound_eq_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  W.tableCertifiedTotalBound = W.tablePrefixBudget + W.tailBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tableCertifiedTotalBound_eq W

/--
[retarget_tableFiniteBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma retarget_tableFiniteBudget_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  (W.retarget N).tableFiniteBudget = W.tableFiniteBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.retarget_tableFiniteBudget W N

/--
[retarget_tablePrefixBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma retarget_tablePrefixBudget_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  (W.retarget N).tablePrefixBudget = W.tablePrefixBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.retarget_tablePrefixBudget W N

/--
[retarget_tableCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma retarget_tableCertifiedTotalBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  (W.retarget N).tableCertifiedTotalBound = W.tableCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.retarget_tableCertifiedTotalBound W N

/--
[tableCertifiedTotalBound_nonneg_of_component_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tableCertifiedTotalBound_nonneg_of_component_nonneg_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hfinite : 0 ≤ W.finiteBound)
  (hprefix : 0 ≤ W.prefixTailBound) :
-- imply
  0 ≤ W.tableCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tableCertifiedTotalBound_nonneg_of_component_nonneg W hfinite hprefix

/--
[tableTailBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tableTailBound_nonneg_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  0 ≤ W.tailBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tableTailBound_nonneg W

/--
[tableCertifiedTotalBound_le_of_component_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tableCertifiedTotalBound_le_of_component_bounds_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {finiteBound' prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hfinite : W.finiteBound ≤ finiteBound')
  (hprefix : W.prefixTailBound ≤ prefixTailBound')
  (htail : W.tailBound ≤ tailBound') :
-- imply
  W.tableCertifiedTotalBound ≤ (W.finitePrefix.card : ℝ) * finiteBound' + prefixTailBound' + tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tableCertifiedTotalBound_le_of_component_bounds W hfinite hprefix htail

/--
[tableCertifiedTotalBound_le_of_tablePrefixBudget_tailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tableCertifiedTotalBound_le_of_tablePrefixBudget_tailBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixBound tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hprefix : W.tablePrefixBudget ≤ prefixBound)
  (htail : W.tailBound ≤ tailBound') :
-- imply
  W.tableCertifiedTotalBound ≤ prefixBound + tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tableCertifiedTotalBound_le_of_tablePrefixBudget_tailBound W hprefix htail

/--
[tailPrefixSum_le_tablePrefixBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailPrefixSum_le_tablePrefixBudget_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  W.tailPrefixSum ≤ W.tablePrefixBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailPrefixSum_le_tablePrefixBudget W

/--
[finiteContribution_le_finiteBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma finiteContribution_le_finiteBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {a : α}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  W.S.finiteContribution a ≤ W.finiteBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.finiteContribution_le_finiteBound W a

/--
[tablePrefixBudget_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tablePrefixBudget_nonneg_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  0 ≤ W.tablePrefixBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tablePrefixBudget_nonneg W

/--
[tailCertifiedTotalBound_le_tableCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailCertifiedTotalBound_le_tableCertifiedTotalBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  W.tailCertifiedTotalBound ≤ W.tableCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailCertifiedTotalBound_le_tableCertifiedTotalBound W

/--
[tail_tsum_le_tableCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tail_tsum_le_tableCertifiedTotalBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  (∑' a, W.tailContribution a) ≤ W.tableCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tail_tsum_le_tableCertifiedTotalBound W

/--
[tail_tsum_le_of_tableCertifiedTotalBound_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tail_tsum_le_of_tableCertifiedTotalBound_le_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {B : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hB : W.tableCertifiedTotalBound ≤ B) :
-- imply
  (∑' a, W.tailContribution a) ≤ B := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tail_tsum_le_of_tableCertifiedTotalBound_le W hB

/--
[tail_tsum_le_tablePrefixBudget_add_tailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tail_tsum_le_tablePrefixBudget_add_tailBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  (∑' a, W.tailContribution a) ≤ W.tablePrefixBudget + W.tailBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tail_tsum_le_tablePrefixBudget_add_tailBound W

/--
[tailTotalTsum_le_tableCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_le_tableCertifiedTotalBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  W.tailTotalTsum ≤ W.tableCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailTotalTsum_le_tableCertifiedTotalBound W

/--
[tableCertifiedTotalBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tableCertifiedTotalBound_nonneg_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  0 ≤ W.tableCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tableCertifiedTotalBound_nonneg W

/--
[tailTotalTsum_le_tablePrefixBudget_add_tailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_le_tablePrefixBudget_add_tailBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M) :
-- imply
  W.tailTotalTsum ≤ W.tablePrefixBudget + W.tailBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailTotalTsum_le_tablePrefixBudget_add_tailBound W

/--
[tailTotalTsum_le_of_tableCertifiedTotalBound_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_le_of_tableCertifiedTotalBound_le_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {B : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hB : W.tableCertifiedTotalBound ≤ B) :
-- imply
  W.tailTotalTsum ≤ B := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.tailTotalTsum_le_of_tableCertifiedTotalBound_le W hB

/--
[with_tailEnvelope_and_budgets_finiteBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_budgets_finiteBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailEnvelope' : α → ℝ}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
  (hprefixSum : (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
  (henvelope_nonneg_off : ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
  (htail_le_tailEnvelope : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
  (hsummable_masked : Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
  (hmasked_tsum_le : (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤ tailBound') :
-- imply
  (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le).finiteBound = W.finiteBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_tailEnvelope_and_budgets_finiteBound W tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le

/--
[with_tailEnvelope_and_budgets_prefixTailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_budgets_prefixTailBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailEnvelope' : α → ℝ}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
  (hprefixSum : (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
  (henvelope_nonneg_off : ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
  (htail_le_tailEnvelope : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
  (hsummable_masked : Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
  (hmasked_tsum_le : (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤ tailBound') :
-- imply
  (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le).prefixTailBound = prefixTailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_tailEnvelope_and_budgets_prefixTailBound W tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le

/--
[with_tailEnvelope_and_budgets_tailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_budgets_tailBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailEnvelope' : α → ℝ}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
  (hprefixSum : (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
  (henvelope_nonneg_off : ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
  (htail_le_tailEnvelope : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
  (hsummable_masked : Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
  (hmasked_tsum_le : (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤ tailBound') :
-- imply
  (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le).tailBound = tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_tailEnvelope_and_budgets_tailBound W tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le

/--
[with_tailEnvelope_and_budgets_tailEnvelope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_budgets_tailEnvelope_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailEnvelope' : α → ℝ}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
  (hprefixSum : (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
  (henvelope_nonneg_off : ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
  (htail_le_tailEnvelope : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
  (hsummable_masked : Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
  (hmasked_tsum_le : (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤ tailBound') :
-- imply
  (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le).tailEnvelope = tailEnvelope' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_tailEnvelope_and_budgets_tailEnvelope W tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le

/--
[with_tailEnvelope_and_budgets_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_budgets_tailBudget_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailEnvelope' : α → ℝ}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
  (hprefixSum : (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
  (henvelope_nonneg_off : ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
  (htail_le_tailEnvelope : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
  (hsummable_masked : Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
  (hmasked_tsum_le : (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤ tailBound') :
-- imply
  (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le).tailBudget = tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_tailEnvelope_and_budgets_tailBudget W tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le

/--
[with_tailEnvelope_and_budgets_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_budgets_tailPrefixSum_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailEnvelope' : α → ℝ}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
  (hprefixSum : (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
  (henvelope_nonneg_off : ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
  (htail_le_tailEnvelope : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
  (hsummable_masked : Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
  (hmasked_tsum_le : (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤ tailBound') :
-- imply
  (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le).tailPrefixSum = W.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_tailEnvelope_and_budgets_tailPrefixSum W tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le

/--
[with_tailEnvelope_and_budgets_tailCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_budgets_tailCertifiedTotalBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailEnvelope' : α → ℝ}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
  (hprefixSum : (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
  (henvelope_nonneg_off : ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
  (htail_le_tailEnvelope : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
  (hsummable_masked : Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
  (hmasked_tsum_le : (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤ tailBound') :
-- imply
  (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le).tailCertifiedTotalBound = W.tailPrefixSum + tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_tailEnvelope_and_budgets_tailCertifiedTotalBound W tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le

/--
[with_tailEnvelope_and_budgets_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_budgets_tailContribution_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailEnvelope' : α → ℝ}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
  (hprefixSum : (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
  (henvelope_nonneg_off : ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
  (htail_le_tailEnvelope : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
  (hsummable_masked : Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
  (hmasked_tsum_le : (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤ tailBound') :
-- imply
  (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le).tailContribution = W.tailContribution := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_tailEnvelope_and_budgets_tailContribution W tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le

/--
[with_tailEnvelope_and_budgets_tailTotalTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_budgets_tailTotalTsum_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailEnvelope' : α → ℝ}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
  (hprefixSum : (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
  (henvelope_nonneg_off : ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
  (htail_le_tailEnvelope : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
  (hsummable_masked : Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
  (hmasked_tsum_le : (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤ tailBound') :
-- imply
  (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le).tailTotalTsum = W.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_tailEnvelope_and_budgets_tailTotalTsum W tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le

/--
[with_tailEnvelope_and_budgets_tailRemainderSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_budgets_tailRemainderSum_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailEnvelope' : α → ℝ}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
  (hprefixSum : (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
  (henvelope_nonneg_off : ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
  (htail_le_tailEnvelope : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
  (hsummable_masked : Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
  (hmasked_tsum_le : (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤ tailBound') :
-- imply
  (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le).tailRemainderSum = W.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_tailEnvelope_and_budgets_tailRemainderSum W tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le

/--
[with_tailEnvelope_and_budgets_tableFiniteBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_budgets_tableFiniteBudget_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailEnvelope' : α → ℝ}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
  (hprefixSum : (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
  (henvelope_nonneg_off : ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
  (htail_le_tailEnvelope : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
  (hsummable_masked : Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
  (hmasked_tsum_le : (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤ tailBound') :
-- imply
  (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le).tableFiniteBudget = W.tableFiniteBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_tailEnvelope_and_budgets_tableFiniteBudget W tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le

/--
[with_tailEnvelope_and_budgets_tablePrefixBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_budgets_tablePrefixBudget_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailEnvelope' : α → ℝ}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
  (hprefixSum : (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
  (henvelope_nonneg_off : ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
  (htail_le_tailEnvelope : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
  (hsummable_masked : Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
  (hmasked_tsum_le : (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤ tailBound') :
-- imply
  (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le).tablePrefixBudget = W.tableFiniteBudget + prefixTailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_tailEnvelope_and_budgets_tablePrefixBudget W tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le

/--
[with_tailEnvelope_and_budgets_tableCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_budgets_tableCertifiedTotalBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailEnvelope' : α → ℝ}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
  (hprefixSum : (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
  (henvelope_nonneg_off : ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
  (htail_le_tailEnvelope : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
  (hsummable_masked : Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
  (hmasked_tsum_le : (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤ tailBound') :
-- imply
  (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le).tableCertifiedTotalBound = (W.finitePrefix.card : ℝ) * W.finiteBound + prefixTailBound' + tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_tailEnvelope_and_budgets_tableCertifiedTotalBound W tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le

/--
[with_tailEnvelope_and_budgets_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_budgets_certificate_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailEnvelope' : α → ℝ}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
  (hprefixSum : (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
  (henvelope_nonneg_off : ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
  (htail_le_tailEnvelope : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
  (hsummable_masked : Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
  (hmasked_tsum_le : (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤ tailBound') :
-- imply
  (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le).certificate = W.certificate := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_tailEnvelope_and_budgets_certificate W tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le

/--
[with_zero_tailEnvelope_and_budgets_finiteBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_zero_tailEnvelope_and_budgets_finiteBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
  (hprefix_nonneg : 0 ≤ prefixTailBound')
  (htail_nonpos : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
  (htailBound_nonneg : 0 ≤ tailBound') :
-- imply
  (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg).finiteBound = W.finiteBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_zero_tailEnvelope_and_budgets_finiteBound W htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg

/--
[with_zero_tailEnvelope_and_budgets_prefixTailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_zero_tailEnvelope_and_budgets_prefixTailBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
  (hprefix_nonneg : 0 ≤ prefixTailBound')
  (htail_nonpos : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
  (htailBound_nonneg : 0 ≤ tailBound') :
-- imply
  (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg).prefixTailBound = prefixTailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_zero_tailEnvelope_and_budgets_prefixTailBound W htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg

/--
[with_zero_tailEnvelope_and_budgets_tailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_zero_tailEnvelope_and_budgets_tailBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
  (hprefix_nonneg : 0 ≤ prefixTailBound')
  (htail_nonpos : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
  (htailBound_nonneg : 0 ≤ tailBound') :
-- imply
  (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg).tailBound = tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_zero_tailEnvelope_and_budgets_tailBound W htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg

/--
[with_zero_tailEnvelope_and_budgets_tailEnvelope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_zero_tailEnvelope_and_budgets_tailEnvelope_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
  (hprefix_nonneg : 0 ≤ prefixTailBound')
  (htail_nonpos : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
  (htailBound_nonneg : 0 ≤ tailBound') :
-- imply
  (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg).tailEnvelope = (fun _ => (0 : ℝ)) := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_zero_tailEnvelope_and_budgets_tailEnvelope W htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg

/--
[with_zero_tailEnvelope_and_budgets_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_zero_tailEnvelope_and_budgets_tailBudget_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
  (hprefix_nonneg : 0 ≤ prefixTailBound')
  (htail_nonpos : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
  (htailBound_nonneg : 0 ≤ tailBound') :
-- imply
  (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg).tailBudget = tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_zero_tailEnvelope_and_budgets_tailBudget W htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg

/--
[with_zero_tailEnvelope_and_budgets_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_zero_tailEnvelope_and_budgets_tailPrefixSum_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
  (hprefix_nonneg : 0 ≤ prefixTailBound')
  (htail_nonpos : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
  (htailBound_nonneg : 0 ≤ tailBound') :
-- imply
  (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg).tailPrefixSum = W.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_zero_tailEnvelope_and_budgets_tailPrefixSum W htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg

/--
[with_zero_tailEnvelope_and_budgets_tailCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_zero_tailEnvelope_and_budgets_tailCertifiedTotalBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
  (hprefix_nonneg : 0 ≤ prefixTailBound')
  (htail_nonpos : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
  (htailBound_nonneg : 0 ≤ tailBound') :
-- imply
  (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg).tailCertifiedTotalBound = W.tailPrefixSum + tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_zero_tailEnvelope_and_budgets_tailCertifiedTotalBound W htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg

/--
[with_zero_tailEnvelope_and_budgets_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_zero_tailEnvelope_and_budgets_tailContribution_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
  (hprefix_nonneg : 0 ≤ prefixTailBound')
  (htail_nonpos : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
  (htailBound_nonneg : 0 ≤ tailBound') :
-- imply
  (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg).tailContribution = W.tailContribution := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_zero_tailEnvelope_and_budgets_tailContribution W htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg

/--
[with_zero_tailEnvelope_and_budgets_tailTotalTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_zero_tailEnvelope_and_budgets_tailTotalTsum_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
  (hprefix_nonneg : 0 ≤ prefixTailBound')
  (htail_nonpos : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
  (htailBound_nonneg : 0 ≤ tailBound') :
-- imply
  (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg).tailTotalTsum = W.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_zero_tailEnvelope_and_budgets_tailTotalTsum W htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg

/--
[with_zero_tailEnvelope_and_budgets_tailRemainderSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_zero_tailEnvelope_and_budgets_tailRemainderSum_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
  (hprefix_nonneg : 0 ≤ prefixTailBound')
  (htail_nonpos : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
  (htailBound_nonneg : 0 ≤ tailBound') :
-- imply
  (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg).tailRemainderSum = W.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_zero_tailEnvelope_and_budgets_tailRemainderSum W htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg

/--
[with_zero_tailEnvelope_and_budgets_tableFiniteBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_zero_tailEnvelope_and_budgets_tableFiniteBudget_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
  (hprefix_nonneg : 0 ≤ prefixTailBound')
  (htail_nonpos : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
  (htailBound_nonneg : 0 ≤ tailBound') :
-- imply
  (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg).tableFiniteBudget = W.tableFiniteBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_zero_tailEnvelope_and_budgets_tableFiniteBudget W htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg

/--
[with_zero_tailEnvelope_and_budgets_tablePrefixBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_zero_tailEnvelope_and_budgets_tablePrefixBudget_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
  (hprefix_nonneg : 0 ≤ prefixTailBound')
  (htail_nonpos : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
  (htailBound_nonneg : 0 ≤ tailBound') :
-- imply
  (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg).tablePrefixBudget = W.tableFiniteBudget + prefixTailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_zero_tailEnvelope_and_budgets_tablePrefixBudget W htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg

/--
[with_zero_tailEnvelope_and_budgets_tableCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_zero_tailEnvelope_and_budgets_tableCertifiedTotalBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
  (hprefix_nonneg : 0 ≤ prefixTailBound')
  (htail_nonpos : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
  (htailBound_nonneg : 0 ≤ tailBound') :
-- imply
  (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg).tableCertifiedTotalBound = (W.finitePrefix.card : ℝ) * W.finiteBound + prefixTailBound' + tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_zero_tailEnvelope_and_budgets_tableCertifiedTotalBound W htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg

/--
[with_zero_tailEnvelope_and_budgets_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_zero_tailEnvelope_and_budgets_certificate_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
  (hprefix_nonneg : 0 ≤ prefixTailBound')
  (htail_nonpos : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
  (htailBound_nonneg : 0 ≤ tailBound') :
-- imply
  (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg).certificate = W.certificate := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_zero_tailEnvelope_and_budgets_certificate W htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg

/--
[with_tailEnvelope_and_budgets_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_budgets_rgToExponentBridge_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailEnvelope' : α → ℝ}
  {prefixTailBound' tailBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
  (hprefixSum : (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
  (henvelope_nonneg_off : ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
  (htail_le_tailEnvelope : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
  (hsummable_masked : Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
  (hmasked_tsum_le : (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤ tailBound')
  (hbridge : W.certificate.RGToExponentBridge correlationLength) :
-- imply
  (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_tailEnvelope_and_budgets_rgToExponentBridge W tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le hbridge

/--
[with_tailEnvelope_and_budgets_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_budgets_valid_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailEnvelope' : α → ℝ}
  {prefixTailBound' tailBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
  (hprefixSum : (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
  (henvelope_nonneg_off : ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
  (htail_le_tailEnvelope : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
  (hsummable_masked : Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
  (hmasked_tsum_le : (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤ tailBound')
  (hvalid : W.certificate.Valid correlationLength) :
-- imply
  (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_tailEnvelope_and_budgets_valid W tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le hvalid

/--
[with_tailEnvelope_and_budgets_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_budgets_hasCriticalNu_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailEnvelope' : α → ℝ}
  {prefixTailBound' tailBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix tailEnvelope')
  (hprefixSum : (∑ a ∈ W.finitePrefix, tailEnvelope' a) ≤ prefixTailBound')
  (henvelope_nonneg_off : ∀ a, a ∉ W.finitePrefix → 0 ≤ tailEnvelope' a)
  (htail_le_tailEnvelope : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ tailEnvelope' a)
  (hsummable_masked : Summable (fun a => if a ∈ W.finitePrefix then 0 else tailEnvelope' a))
  (hmasked_tsum_le : (∑' a, (if a ∈ W.finitePrefix then 0 else tailEnvelope' a)) ≤ tailBound')
  (hν : HasCriticalNu M correlationLength W.certificate.predictedExponent) :
-- imply
  HasCriticalNu M correlationLength (W.with_tailEnvelope_and_budgets tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_tailEnvelope_and_budgets_hasCriticalNu W tailEnvelope' htailOnPrefix hprefixSum henvelope_nonneg_off htail_le_tailEnvelope hsummable_masked hmasked_tsum_le hν

/--
[with_zero_tailEnvelope_and_budgets_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_zero_tailEnvelope_and_budgets_rgToExponentBridge_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' tailBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
  (hprefix_nonneg : 0 ≤ prefixTailBound')
  (htail_nonpos : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
  (htailBound_nonneg : 0 ≤ tailBound')
  (hbridge : W.certificate.RGToExponentBridge correlationLength) :
-- imply
  (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_zero_tailEnvelope_and_budgets_rgToExponentBridge W htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg hbridge

/--
[with_zero_tailEnvelope_and_budgets_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_zero_tailEnvelope_and_budgets_valid_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' tailBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
  (hprefix_nonneg : 0 ≤ prefixTailBound')
  (htail_nonpos : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
  (htailBound_nonneg : 0 ≤ tailBound')
  (hvalid : W.certificate.Valid correlationLength) :
-- imply
  (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_zero_tailEnvelope_and_budgets_valid W htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg hvalid

/--
[with_zero_tailEnvelope_and_budgets_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_zero_tailEnvelope_and_budgets_hasCriticalNu_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' tailBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (htailOnPrefix : W.S.TailEnvelopeOn W.finitePrefix (fun _ => (0 : ℝ)))
  (hprefix_nonneg : 0 ≤ prefixTailBound')
  (htail_nonpos : ∀ a, a ∉ W.finitePrefix → W.S.tailContribution a ≤ 0)
  (htailBound_nonneg : 0 ≤ tailBound')
  (hν : HasCriticalNu M correlationLength W.certificate.predictedExponent) :
-- imply
  HasCriticalNu M correlationLength (W.with_zero_tailEnvelope_and_budgets htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_zero_tailEnvelope_and_budgets_hasCriticalNu W htailOnPrefix hprefix_nonneg htail_nonpos htailBound_nonneg hν

/--
[with_larger_finiteBound_finiteBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_finiteBound_finiteBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {finiteBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.finiteBound ≤ finiteBound') :
-- imply
  (W.with_larger_finiteBound hle).finiteBound = finiteBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_finiteBound_finiteBound W hle

/--
[with_larger_finiteBound_prefixTailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_finiteBound_prefixTailBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {finiteBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.finiteBound ≤ finiteBound') :
-- imply
  (W.with_larger_finiteBound hle).prefixTailBound = W.prefixTailBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_finiteBound_prefixTailBound W hle

/--
[with_larger_finiteBound_tailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_finiteBound_tailBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {finiteBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.finiteBound ≤ finiteBound') :
-- imply
  (W.with_larger_finiteBound hle).tailBound = W.tailBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_finiteBound_tailBound W hle

/--
[with_larger_finiteBound_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_finiteBound_tailBudget_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {finiteBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.finiteBound ≤ finiteBound') :
-- imply
  (W.with_larger_finiteBound hle).tailBudget = W.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_finiteBound_tailBudget W hle

/--
[with_larger_finiteBound_tableFiniteBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_finiteBound_tableFiniteBudget_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {finiteBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.finiteBound ≤ finiteBound') :
-- imply
  (W.with_larger_finiteBound hle).tableFiniteBudget = (W.finitePrefix.card : ℝ) * finiteBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_finiteBound_tableFiniteBudget W hle

/--
[with_larger_finiteBound_tablePrefixBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_finiteBound_tablePrefixBudget_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {finiteBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.finiteBound ≤ finiteBound') :
-- imply
  (W.with_larger_finiteBound hle).tablePrefixBudget = (W.finitePrefix.card : ℝ) * finiteBound' + W.prefixTailBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_finiteBound_tablePrefixBudget W hle

/--
[with_larger_finiteBound_tableCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_finiteBound_tableCertifiedTotalBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {finiteBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.finiteBound ≤ finiteBound') :
-- imply
  (W.with_larger_finiteBound hle).tableCertifiedTotalBound = (W.finitePrefix.card : ℝ) * finiteBound' + W.prefixTailBound + W.tailBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_finiteBound_tableCertifiedTotalBound W hle

/--
[with_larger_finiteBound_toWitnessPackage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_finiteBound_toWitnessPackage_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {finiteBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.finiteBound ≤ finiteBound') :
-- imply
  (W.with_larger_finiteBound hle).toWitnessPackage = W.toWitnessPackage := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_finiteBound_toWitnessPackage W hle

/--
[with_larger_finiteBound_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_finiteBound_certificate_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {finiteBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.finiteBound ≤ finiteBound') :
-- imply
  (W.with_larger_finiteBound hle).certificate = W.certificate := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_finiteBound_certificate W hle

/--
[with_larger_finiteBound_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_finiteBound_tailContribution_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {finiteBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.finiteBound ≤ finiteBound') :
-- imply
  (W.with_larger_finiteBound hle).tailContribution = W.tailContribution := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_finiteBound_tailContribution W hle

/--
[with_larger_finiteBound_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_finiteBound_tailPrefixSum_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {finiteBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.finiteBound ≤ finiteBound') :
-- imply
  (W.with_larger_finiteBound hle).tailPrefixSum = W.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_finiteBound_tailPrefixSum W hle

/--
[with_larger_finiteBound_tailCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_finiteBound_tailCertifiedTotalBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {finiteBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.finiteBound ≤ finiteBound') :
-- imply
  (W.with_larger_finiteBound hle).tailCertifiedTotalBound = W.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_finiteBound_tailCertifiedTotalBound W hle

/--
[with_larger_finiteBound_tailTotalTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_finiteBound_tailTotalTsum_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {finiteBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.finiteBound ≤ finiteBound') :
-- imply
  (W.with_larger_finiteBound hle).tailTotalTsum = W.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_finiteBound_tailTotalTsum W hle

/--
[with_larger_finiteBound_tailRemainderSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_finiteBound_tailRemainderSum_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {finiteBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.finiteBound ≤ finiteBound') :
-- imply
  (W.with_larger_finiteBound hle).tailRemainderSum = W.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_finiteBound_tailRemainderSum W hle

/--
[with_larger_finiteBound_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_finiteBound_rgToExponentBridge_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {finiteBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.finiteBound ≤ finiteBound')
  (hbridge : W.certificate.RGToExponentBridge correlationLength) :
-- imply
  (W.with_larger_finiteBound hle).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_finiteBound_rgToExponentBridge W hle hbridge

/--
[with_larger_finiteBound_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_finiteBound_valid_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {finiteBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.finiteBound ≤ finiteBound')
  (hvalid : W.certificate.Valid correlationLength) :
-- imply
  (W.with_larger_finiteBound hle).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_finiteBound_valid W hle hvalid

/--
[with_larger_finiteBound_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_finiteBound_hasCriticalNu_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {finiteBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.finiteBound ≤ finiteBound')
  (hν : HasCriticalNu M correlationLength W.certificate.predictedExponent) :
-- imply
  HasCriticalNu M correlationLength (W.with_larger_finiteBound hle).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_finiteBound_hasCriticalNu W hle hν

/--
[with_larger_prefixTailBound_finiteBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_prefixTailBound_finiteBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.prefixTailBound ≤ prefixTailBound') :
-- imply
  (W.with_larger_prefixTailBound hle).finiteBound = W.finiteBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_prefixTailBound_finiteBound W hle

/--
[with_larger_prefixTailBound_prefixTailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_prefixTailBound_prefixTailBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.prefixTailBound ≤ prefixTailBound') :
-- imply
  (W.with_larger_prefixTailBound hle).prefixTailBound = prefixTailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_prefixTailBound_prefixTailBound W hle

/--
[with_larger_prefixTailBound_tailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_prefixTailBound_tailBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.prefixTailBound ≤ prefixTailBound') :
-- imply
  (W.with_larger_prefixTailBound hle).tailBound = W.tailBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_prefixTailBound_tailBound W hle

/--
[with_larger_prefixTailBound_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_prefixTailBound_tailBudget_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.prefixTailBound ≤ prefixTailBound') :
-- imply
  (W.with_larger_prefixTailBound hle).tailBudget = W.tailBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_prefixTailBound_tailBudget W hle

/--
[with_larger_prefixTailBound_tableFiniteBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_prefixTailBound_tableFiniteBudget_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.prefixTailBound ≤ prefixTailBound') :
-- imply
  (W.with_larger_prefixTailBound hle).tableFiniteBudget = W.tableFiniteBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_prefixTailBound_tableFiniteBudget W hle

/--
[with_larger_prefixTailBound_tablePrefixBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_prefixTailBound_tablePrefixBudget_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.prefixTailBound ≤ prefixTailBound') :
-- imply
  (W.with_larger_prefixTailBound hle).tablePrefixBudget = W.tableFiniteBudget + prefixTailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_prefixTailBound_tablePrefixBudget W hle

/--
[with_larger_prefixTailBound_tableCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_prefixTailBound_tableCertifiedTotalBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.prefixTailBound ≤ prefixTailBound') :
-- imply
  (W.with_larger_prefixTailBound hle).tableCertifiedTotalBound = (W.finitePrefix.card : ℝ) * W.finiteBound + prefixTailBound' + W.tailBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_prefixTailBound_tableCertifiedTotalBound W hle

/--
[with_larger_prefixTailBound_toWitnessPackage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_prefixTailBound_toWitnessPackage_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.prefixTailBound ≤ prefixTailBound') :
-- imply
  (W.with_larger_prefixTailBound hle).toWitnessPackage = W.toWitnessPackage := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_prefixTailBound_toWitnessPackage W hle

/--
[with_larger_prefixTailBound_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_prefixTailBound_certificate_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.prefixTailBound ≤ prefixTailBound') :
-- imply
  (W.with_larger_prefixTailBound hle).certificate = W.certificate := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_prefixTailBound_certificate W hle

/--
[with_larger_prefixTailBound_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_prefixTailBound_tailContribution_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.prefixTailBound ≤ prefixTailBound') :
-- imply
  (W.with_larger_prefixTailBound hle).tailContribution = W.tailContribution := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_prefixTailBound_tailContribution W hle

/--
[with_larger_prefixTailBound_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_prefixTailBound_tailPrefixSum_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.prefixTailBound ≤ prefixTailBound') :
-- imply
  (W.with_larger_prefixTailBound hle).tailPrefixSum = W.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_prefixTailBound_tailPrefixSum W hle

/--
[with_larger_prefixTailBound_tailCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_prefixTailBound_tailCertifiedTotalBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.prefixTailBound ≤ prefixTailBound') :
-- imply
  (W.with_larger_prefixTailBound hle).tailCertifiedTotalBound = W.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_prefixTailBound_tailCertifiedTotalBound W hle

/--
[with_larger_prefixTailBound_tailTotalTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_prefixTailBound_tailTotalTsum_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.prefixTailBound ≤ prefixTailBound') :
-- imply
  (W.with_larger_prefixTailBound hle).tailTotalTsum = W.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_prefixTailBound_tailTotalTsum W hle

/--
[with_larger_prefixTailBound_tailRemainderSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_prefixTailBound_tailRemainderSum_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.prefixTailBound ≤ prefixTailBound') :
-- imply
  (W.with_larger_prefixTailBound hle).tailRemainderSum = W.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_prefixTailBound_tailRemainderSum W hle

/--
[with_larger_prefixTailBound_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_prefixTailBound_rgToExponentBridge_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.prefixTailBound ≤ prefixTailBound')
  (hbridge : W.certificate.RGToExponentBridge correlationLength) :
-- imply
  (W.with_larger_prefixTailBound hle).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_prefixTailBound_rgToExponentBridge W hle hbridge

/--
[with_larger_prefixTailBound_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_prefixTailBound_valid_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.prefixTailBound ≤ prefixTailBound')
  (hvalid : W.certificate.Valid correlationLength) :
-- imply
  (W.with_larger_prefixTailBound hle).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_prefixTailBound_valid W hle hvalid

/--
[with_larger_prefixTailBound_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_prefixTailBound_hasCriticalNu_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {prefixTailBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.prefixTailBound ≤ prefixTailBound')
  (hν : HasCriticalNu M correlationLength W.certificate.predictedExponent) :
-- imply
  HasCriticalNu M correlationLength (W.with_larger_prefixTailBound hle).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_prefixTailBound_hasCriticalNu W hle hν

/--
[with_larger_tailBound_finiteBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBound_finiteBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.tailBound ≤ tailBound') :
-- imply
  (W.with_larger_tailBound hle).finiteBound = W.finiteBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_tailBound_finiteBound W hle

/--
[with_larger_tailBound_prefixTailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBound_prefixTailBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.tailBound ≤ tailBound') :
-- imply
  (W.with_larger_tailBound hle).prefixTailBound = W.prefixTailBound := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_tailBound_prefixTailBound W hle

/--
[with_larger_tailBound_tailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBound_tailBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.tailBound ≤ tailBound') :
-- imply
  (W.with_larger_tailBound hle).tailBound = tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_tailBound_tailBound W hle

/--
[with_larger_tailBound_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBound_tailBudget_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.tailBound ≤ tailBound') :
-- imply
  (W.with_larger_tailBound hle).tailBudget = tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_tailBound_tailBudget W hle

/--
[with_larger_tailBound_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBound_tailPrefixSum_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.tailBound ≤ tailBound') :
-- imply
  (W.with_larger_tailBound hle).tailPrefixSum = W.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_tailBound_tailPrefixSum W hle

/--
[with_larger_tailBound_tailCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBound_tailCertifiedTotalBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.tailBound ≤ tailBound') :
-- imply
  (W.with_larger_tailBound hle).tailCertifiedTotalBound = W.tailPrefixSum + tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_tailBound_tailCertifiedTotalBound W hle

/--
[with_larger_tailBound_tableFiniteBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBound_tableFiniteBudget_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.tailBound ≤ tailBound') :
-- imply
  (W.with_larger_tailBound hle).tableFiniteBudget = W.tableFiniteBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_tailBound_tableFiniteBudget W hle

/--
[with_larger_tailBound_tablePrefixBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBound_tablePrefixBudget_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.tailBound ≤ tailBound') :
-- imply
  (W.with_larger_tailBound hle).tablePrefixBudget = W.tablePrefixBudget := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_tailBound_tablePrefixBudget W hle

/--
[with_larger_tailBound_tableCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBound_tableCertifiedTotalBound_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.tailBound ≤ tailBound') :
-- imply
  (W.with_larger_tailBound hle).tableCertifiedTotalBound = (W.finitePrefix.card : ℝ) * W.finiteBound + W.prefixTailBound + tailBound' := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_tailBound_tableCertifiedTotalBound W hle

/--
[with_larger_tailBound_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBound_tailContribution_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.tailBound ≤ tailBound') :
-- imply
  (W.with_larger_tailBound hle).tailContribution = W.tailContribution := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_tailBound_tailContribution W hle

/--
[with_larger_tailBound_tailTotalTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBound_tailTotalTsum_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.tailBound ≤ tailBound') :
-- imply
  (W.with_larger_tailBound hle).tailTotalTsum = W.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_tailBound_tailTotalTsum W hle

/--
[with_larger_tailBound_tailRemainderSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBound_tailRemainderSum_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.tailBound ≤ tailBound') :
-- imply
  (W.with_larger_tailBound hle).tailRemainderSum = W.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_tailBound_tailRemainderSum W hle

/--
[with_larger_tailBound_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBound_certificate_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.tailBound ≤ tailBound') :
-- imply
  (W.with_larger_tailBound hle).certificate = W.certificate := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_tailBound_certificate W hle

/--
[with_larger_tailBound_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBound_rgToExponentBridge_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.tailBound ≤ tailBound')
  (hbridge : W.certificate.RGToExponentBridge correlationLength) :
-- imply
  (W.with_larger_tailBound hle).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_tailBound_rgToExponentBridge W hle hbridge

/--
[with_larger_tailBound_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBound_valid_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.tailBound ≤ tailBound')
  (hvalid : W.certificate.Valid correlationLength) :
-- imply
  (W.with_larger_tailBound hle).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_tailBound_valid W hle hvalid

/--
[with_larger_tailBound_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBound_hasCriticalNu_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hle : W.tailBound ≤ tailBound')
  (hν : HasCriticalNu M correlationLength W.certificate.predictedExponent) :
-- imply
  HasCriticalNu M correlationLength (W.with_larger_tailBound hle).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.with_larger_tailBound_hasCriticalNu W hle hν

/--
[valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma valid_of_bridge_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.valid_of_bridge W hbridge

/--
[hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma hasCriticalNu_of_bridge_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.hasCriticalNu_of_bridge W hbridge

/--
[rgToExponentBridge_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma rgToExponentBridge_of_bridge_congr_predictedExponent_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.rgToExponentBridge_of_bridge_congr_predictedExponent W hpred hbridge

/--
[valid_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma valid_of_bridge_congr_predictedExponent_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.valid_of_bridge_congr_predictedExponent W hpred hbridge

/--
[hasCriticalNu_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma hasCriticalNu_of_bridge_congr_predictedExponent_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.hasCriticalNu_of_bridge_congr_predictedExponent W hpred hbridge

/--
[rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma rgToExponentBridge_of_hasCriticalNu_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hν : HasCriticalNu M correlationLength W.certificate.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.rgToExponentBridge_of_hasCriticalNu W hν

/--
[valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailMaskedTableWitnessPackage.lean)
-/
@[path]
private lemma valid_of_hasCriticalNu_eq
  [DecidableEq Case]
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (W : InfiniteTailMaskedTableWitnessPackage (Case := Case) (α := α) M)
  (hν : HasCriticalNu M correlationLength W.certificate.predictedExponent) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.InfiniteTailMaskedTableWitnessPackage.valid_of_hasCriticalNu W hν


-- created on 2026-10-23
