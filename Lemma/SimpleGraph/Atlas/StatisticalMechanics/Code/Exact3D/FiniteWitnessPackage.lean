import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part9
open StatMech StatMech.Exact3D StatMech.Exact3D.RGCertificate StatMech.Exact3D.FiniteStableWitness StatMech.Exact3D.FiniteWitnessPackage


/--
[FiniteChecks.valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma valid_of_bridge_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (h : C.FiniteChecks)
  (hbridge : C.RGToExponentBridge correlationLength) :
-- imply
  C.Valid correlationLength where finiteCaseChecks := by
-- proof
  apply StatMech.Exact3D.RGCertificate.FiniteChecks.valid_of_bridge h hbridge

/--
[FiniteChecks.hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma hasCriticalNu_of_bridge_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (h : C.FiniteChecks)
  (hbridge : C.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu M correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.FiniteChecks.hasCriticalNu_of_bridge h hbridge

/--
[FiniteChecks.rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma rgToExponentBridge_of_hasCriticalNu_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (_h : C.FiniteChecks)
  (hν : HasCriticalNu M correlationLength C.predictedExponent) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.FiniteChecks.rgToExponentBridge_of_hasCriticalNu _h hν

/--
[FiniteChecks.valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma valid_of_hasCriticalNu_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (h : C.FiniteChecks)
  (hν : HasCriticalNu M correlationLength C.predictedExponent) :
-- imply
  C.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.FiniteChecks.valid_of_hasCriticalNu h hν

/--
[fixedPoint_isFixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma fixedPoint_isFixed_eq
  {n : ℕ}
  {S : FiniteStableWitness n} :
-- imply
  S.map S.fixedPoint = S.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FiniteStableWitness.fixedPoint_isFixed S

/--
[exists_unique_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma exists_unique_fixedPoint_eq
  {n : ℕ}
  {S : FiniteStableWitness n} :
-- imply
  ∃! p : Fin n → ℝ, S.map p = p := by
-- proof
  apply StatMech.Exact3D.FiniteStableWitness.exists_unique_fixedPoint S

/--
[fixedPoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma fixedPoint_mem_eq
  {n : ℕ}
  {S : FiniteStableWitness n} :
-- imply
  FiniteContraction.ClosedBall S.contraction.center S.contraction.radius S.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FiniteStableWitness.fixedPoint_mem S

/--
[rgMap_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma rgMap_scale_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  W.rgMap.scale = W.scale := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgMap_scale W

/--
[fixedPoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma fixedPoint_eq_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  W.rgMap.map W.fixedPoint = W.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.fixedPoint_eq W

/--
[certificate_scale_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma certificate_scale_eq_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  W.certificate.scale = W.scale := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.certificate_scale_eq W

/--
[certificate_thermalEigenvalue_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma certificate_thermalEigenvalue_eq_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  W.certificate.thermalEigenvalue = W.thermal := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.certificate_thermalEigenvalue_eq W

/--
[certificate_fixedPoint_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma certificate_fixedPoint_eq_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  W.certificate.fixedPointData.fixedPoint = W.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.certificate_fixedPoint_eq W

/--
[certificate_predictedExponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma certificate_predictedExponent_eq_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  W.certificate.predictedExponent = predictedNu W.scale W.thermal := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.certificate_predictedExponent_eq W

/--
[retarget_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma retarget_certificate_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  (W.retarget N).certificate = W.certificate.retarget N := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.retarget_certificate W N

/--
[retarget_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma retarget_rgToExponentBridge_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength)
  (hβc : M.betaC = N.betaC) :
-- imply
  (W.retarget N).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.retarget_rgToExponentBridge W N hbridge hβc

/--
[retarget_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma retarget_valid_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hvalid : W.certificate.Valid correlationLength)
  (hβc : M.betaC = N.betaC) :
-- imply
  (W.retarget N).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.retarget_valid W N hvalid hβc

/--
[retarget_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma retarget_hasCriticalNu_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hν : HasCriticalNu M correlationLength W.certificate.predictedExponent)
  (hβc : M.betaC = N.betaC) :
-- imply
  HasCriticalNu N correlationLength ((W.retarget N).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.retarget_hasCriticalNu W N hν hβc

/--
[retarget_rgToExponentBridge_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma retarget_rgToExponentBridge_iff_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hβc : M.betaC = N.betaC) :
-- imply
  W.certificate.RGToExponentBridge correlationLength ↔ (W.retarget N).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.retarget_rgToExponentBridge_iff W N hβc

/--
[retarget_valid_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma retarget_valid_iff_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hβc : M.betaC = N.betaC) :
-- imply
  W.certificate.Valid correlationLength ↔ (W.retarget N).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.retarget_valid_iff W N hβc

/--
[retarget_hasCriticalNu_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma retarget_hasCriticalNu_iff_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hβc : M.betaC = N.betaC) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent ↔ HasCriticalNu N correlationLength ((W.retarget N).certificate).predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.retarget_hasCriticalNu_iff W N hβc

/--
[fixedPointEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma fixedPointEnclosure_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  W.certificate.FixedPointEnclosure := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.fixedPointEnclosure W

/--
[finiteChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma finiteChecks_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  W.certificate.FiniteChecks where finiteCaseChecks := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.finiteChecks W

/--
[finiteCaseChecks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma finiteCaseChecks_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  W.certificate.FiniteCaseChecks := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.finiteCaseChecks W

/--
[tailBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tailBounds_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  W.certificate.TailBounds := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tailBounds W

/--
[linearizationEnclosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma linearizationEnclosure_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  W.certificate.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.linearizationEnclosure W

/--
[hyperbolicSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma hyperbolicSplitting_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  W.certificate.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hyperbolicSplitting W

/--
[orbitEntry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma orbitEntry_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  W.certificate.OrbitEntry := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.orbitEntry W

/--
[retarget_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma retarget_tailPrefixSum_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  (W.retarget N).tailPrefixSum = W.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.retarget_tailPrefixSum W N

/--
[retarget_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma retarget_tailBudget_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  (W.retarget N).tailBudget = W.tailBudget := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.retarget_tailBudget W N

/--
[retarget_tailCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma retarget_tailCertifiedTotalBound_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  (W.retarget N).tailCertifiedTotalBound = W.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.retarget_tailCertifiedTotalBound W N

/--
[retarget_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma retarget_tailContribution_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  (W.retarget N).tailContribution = W.tailContribution := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.retarget_tailContribution W N

/--
[retarget_tailTotalTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma retarget_tailTotalTsum_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  (W.retarget N).tailTotalTsum = W.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.retarget_tailTotalTsum W N

/--
[retarget_tailSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma retarget_tailSupport_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  (W.retarget N).tailSupport = W.tailSupport := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.retarget_tailSupport W N

/--
[retarget_tailRemainderSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma retarget_tailRemainderSum_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  (W.retarget N).tailRemainderSum = W.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.retarget_tailRemainderSum W N

/--
[retarget_tailEnvelopeSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma retarget_tailEnvelopeSum_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  (W.retarget N).tailEnvelopeSum = W.tailEnvelopeSum := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.retarget_tailEnvelopeSum W N

/--
[retarget_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma retarget_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {N : CriticalModel κ}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  (W.retarget N).certificate.predictedExponent = W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.retarget_predictedExponent W N

/--
[tailTotalTsum_eq_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_eq_tsum_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  W.tailTotalTsum = ∑' a, W.tailCertificate.weight a := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tailTotalTsum_eq_tsum W

/--
[tailTotalTsum_eq_prefix_add_remainder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_eq_prefix_add_remainder_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  W.tailTotalTsum = W.tailPrefixSum + W.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tailTotalTsum_eq_prefix_add_remainder W

/--
[tailRemainderSum_le_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tailRemainderSum_le_tailBudget_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  W.tailRemainderSum ≤ W.tailBudget := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tailRemainderSum_le_tailBudget W

/--
[tailRemainderSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tailRemainderSum_nonneg_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  0 ≤ W.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tailRemainderSum_nonneg W

/--
[tailSupport_eq_empty_of_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tailSupport_eq_empty_of_support_subset_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hsupport_subset_prefix : W.tailCertificate.support ⊆ W.tailCertificate.finitePrefix) :
-- imply
  W.tailSupport = ∅ := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tailSupport_eq_empty_of_support_subset W hsupport_subset_prefix

/--
[tailTotalTsum_eq_tailPrefixSum_of_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_eq_tailPrefixSum_of_support_subset_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hsupport_subset_prefix : W.tailCertificate.support ⊆ W.tailCertificate.finitePrefix) :
-- imply
  W.tailTotalTsum = W.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tailTotalTsum_eq_tailPrefixSum_of_support_subset W hsupport_subset_prefix

/--
[tailRemainderSum_eq_zero_of_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tailRemainderSum_eq_zero_of_support_subset_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hsupport_subset_prefix : W.tailCertificate.support ⊆ W.tailCertificate.finitePrefix) :
-- imply
  W.tailRemainderSum = 0 := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tailRemainderSum_eq_zero_of_support_subset W hsupport_subset_prefix

/--
[tailRemainderSum_eq_zero_of_tailBudget_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tailRemainderSum_eq_zero_of_tailBudget_eq_zero_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hbudget : W.tailBudget = 0) :
-- imply
  W.tailRemainderSum = 0 := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tailRemainderSum_eq_zero_of_tailBudget_eq_zero W hbudget

/--
[tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hbudget : W.tailBudget = 0) :
-- imply
  W.tailTotalTsum = W.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tailTotalTsum_eq_tailPrefixSum_of_tailBudget_eq_zero W hbudget

/--
[tailEnvelopeSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tailEnvelopeSum_nonneg_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  0 ≤ W.tailEnvelopeSum := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tailEnvelopeSum_nonneg W

/--
[tailEnvelopeSum_le_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tailEnvelopeSum_le_tailBudget_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  W.tailEnvelopeSum ≤ W.tailBudget := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tailEnvelopeSum_le_tailBudget W

/--
[tail_tsum_le_prefix_add_tailBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tail_tsum_le_prefix_add_tailBound_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  (∑' a, W.tailCertificate.weight a) ≤ (∑ a ∈ W.tailCertificate.finitePrefix, W.tailCertificate.weight a) + W.tailCertificate.tailBound := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tail_tsum_le_prefix_add_tailBound W

/--
[tail_tsum_le_certifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tail_tsum_le_certifiedTotalBound_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  (∑' a, W.tailCertificate.weight a) ≤ W.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tail_tsum_le_certifiedTotalBound W

/--
[tail_tsum_le_of_certifiedTotalBound_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tail_tsum_le_of_certifiedTotalBound_le_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {B : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hB : W.tailCertifiedTotalBound ≤ B) :
-- imply
  (∑' a, W.tailCertificate.weight a) ≤ B := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tail_tsum_le_of_certifiedTotalBound_le W hB

/--
[tailTotalTsum_le_certifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_le_certifiedTotalBound_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  W.tailTotalTsum ≤ W.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tailTotalTsum_le_certifiedTotalBound W

/--
[tailTotalTsum_le_of_certifiedTotalBound_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_le_of_certifiedTotalBound_le_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {B : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hB : W.tailCertifiedTotalBound ≤ B) :
-- imply
  W.tailTotalTsum ≤ B := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tailTotalTsum_le_of_certifiedTotalBound_le W hB

/--
[with_tailEnvelope_and_tailBudget_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_tailBudget_tailBudget_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {envelope' : α → ℝ}
  {tailBound' : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (henvelope_nonneg : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
  (hweight_le : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → W.tailCertificate.weight a ≤ envelope' a)
  (henvelope_sum : (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix, envelope' a) ≤ tailBound') :
-- imply
  (W.with_tailEnvelope_and_tailBudget envelope' henvelope_nonneg hweight_le henvelope_sum).tailBudget = tailBound' := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_tailEnvelope_and_tailBudget_tailBudget W envelope' henvelope_nonneg hweight_le henvelope_sum

/--
[with_tailEnvelope_and_tailBudget_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_tailBudget_tailPrefixSum_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {envelope' : α → ℝ}
  {tailBound' : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (henvelope_nonneg : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
  (hweight_le : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → W.tailCertificate.weight a ≤ envelope' a)
  (henvelope_sum : (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix, envelope' a) ≤ tailBound') :
-- imply
  (W.with_tailEnvelope_and_tailBudget envelope' henvelope_nonneg hweight_le henvelope_sum).tailPrefixSum = W.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_tailEnvelope_and_tailBudget_tailPrefixSum W envelope' henvelope_nonneg hweight_le henvelope_sum

/--
[with_tailEnvelope_and_tailBudget_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_tailBudget_certificate_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {envelope' : α → ℝ}
  {tailBound' : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (henvelope_nonneg : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
  (hweight_le : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → W.tailCertificate.weight a ≤ envelope' a)
  (henvelope_sum : (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix, envelope' a) ≤ tailBound') :
-- imply
  (W.with_tailEnvelope_and_tailBudget envelope' henvelope_nonneg hweight_le henvelope_sum).certificate = W.certificate := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_tailEnvelope_and_tailBudget_certificate W envelope' henvelope_nonneg hweight_le henvelope_sum

/--
[with_tailEnvelope_and_tailBudget_tailCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_tailBudget_tailCertifiedTotalBound_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {envelope' : α → ℝ}
  {tailBound' : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (henvelope_nonneg : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
  (hweight_le : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → W.tailCertificate.weight a ≤ envelope' a)
  (henvelope_sum : (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix, envelope' a) ≤ tailBound') :
-- imply
  (W.with_tailEnvelope_and_tailBudget envelope' henvelope_nonneg hweight_le henvelope_sum).tailCertifiedTotalBound = W.tailPrefixSum + tailBound' := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_tailEnvelope_and_tailBudget_tailCertifiedTotalBound W envelope' henvelope_nonneg hweight_le henvelope_sum

/--
[with_tailEnvelope_and_tailBudget_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_tailBudget_tailContribution_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {envelope' : α → ℝ}
  {tailBound' : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (henvelope_nonneg : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
  (hweight_le : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → W.tailCertificate.weight a ≤ envelope' a)
  (henvelope_sum : (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix, envelope' a) ≤ tailBound') :
-- imply
  (W.with_tailEnvelope_and_tailBudget envelope' henvelope_nonneg hweight_le henvelope_sum).tailContribution = W.tailContribution := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_tailEnvelope_and_tailBudget_tailContribution W envelope' henvelope_nonneg hweight_le henvelope_sum

/--
[with_tailEnvelope_and_tailBudget_tailTotalTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_tailBudget_tailTotalTsum_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {envelope' : α → ℝ}
  {tailBound' : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (henvelope_nonneg : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
  (hweight_le : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → W.tailCertificate.weight a ≤ envelope' a)
  (henvelope_sum : (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix, envelope' a) ≤ tailBound') :
-- imply
  (W.with_tailEnvelope_and_tailBudget envelope' henvelope_nonneg hweight_le henvelope_sum).tailTotalTsum = W.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_tailEnvelope_and_tailBudget_tailTotalTsum W envelope' henvelope_nonneg hweight_le henvelope_sum

/--
[with_tailEnvelope_and_tailBudget_tailSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_tailBudget_tailSupport_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {envelope' : α → ℝ}
  {tailBound' : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (henvelope_nonneg : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
  (hweight_le : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → W.tailCertificate.weight a ≤ envelope' a)
  (henvelope_sum : (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix, envelope' a) ≤ tailBound') :
-- imply
  (W.with_tailEnvelope_and_tailBudget envelope' henvelope_nonneg hweight_le henvelope_sum).tailSupport = W.tailSupport := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_tailEnvelope_and_tailBudget_tailSupport W envelope' henvelope_nonneg hweight_le henvelope_sum

/--
[with_tailEnvelope_and_tailBudget_tailRemainderSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_tailBudget_tailRemainderSum_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {envelope' : α → ℝ}
  {tailBound' : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (henvelope_nonneg : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
  (hweight_le : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → W.tailCertificate.weight a ≤ envelope' a)
  (henvelope_sum : (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix, envelope' a) ≤ tailBound') :
-- imply
  (W.with_tailEnvelope_and_tailBudget envelope' henvelope_nonneg hweight_le henvelope_sum).tailRemainderSum = W.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_tailEnvelope_and_tailBudget_tailRemainderSum W envelope' henvelope_nonneg hweight_le henvelope_sum

/--
[with_tailEnvelope_and_tailBudget_tailEnvelopeSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_tailBudget_tailEnvelopeSum_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {envelope' : α → ℝ}
  {tailBound' : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (henvelope_nonneg : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
  (hweight_le : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → W.tailCertificate.weight a ≤ envelope' a)
  (henvelope_sum : (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix, envelope' a) ≤ tailBound') :
-- imply
  (W.with_tailEnvelope_and_tailBudget envelope' henvelope_nonneg hweight_le henvelope_sum).tailEnvelopeSum = ∑ a ∈ W.tailSupport, envelope' a := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_tailEnvelope_and_tailBudget_tailEnvelopeSum W envelope' henvelope_nonneg hweight_le henvelope_sum

/--
[with_tailEnvelope_and_tailBudget_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_tailBudget_rgToExponentBridge_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {envelope' : α → ℝ}
  {tailBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (henvelope_nonneg : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
  (hweight_le : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → W.tailCertificate.weight a ≤ envelope' a)
  (henvelope_sum : (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix, envelope' a) ≤ tailBound')
  (hbridge : W.certificate.RGToExponentBridge correlationLength) :
-- imply
  (W.with_tailEnvelope_and_tailBudget envelope' henvelope_nonneg hweight_le henvelope_sum).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_tailEnvelope_and_tailBudget_rgToExponentBridge W envelope' henvelope_nonneg hweight_le henvelope_sum hbridge

/--
[with_tailEnvelope_and_tailBudget_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_tailBudget_valid_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {envelope' : α → ℝ}
  {tailBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (henvelope_nonneg : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
  (hweight_le : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → W.tailCertificate.weight a ≤ envelope' a)
  (henvelope_sum : (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix, envelope' a) ≤ tailBound')
  (hvalid : W.certificate.Valid correlationLength) :
-- imply
  (W.with_tailEnvelope_and_tailBudget envelope' henvelope_nonneg hweight_le henvelope_sum).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_tailEnvelope_and_tailBudget_valid W envelope' henvelope_nonneg hweight_le henvelope_sum hvalid

/--
[with_tailEnvelope_and_tailBudget_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_tailEnvelope_and_tailBudget_hasCriticalNu_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {envelope' : α → ℝ}
  {tailBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (henvelope_nonneg : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → 0 ≤ envelope' a)
  (hweight_le : ∀ a, a ∈ W.tailCertificate.support → a ∉ W.tailCertificate.finitePrefix → W.tailCertificate.weight a ≤ envelope' a)
  (henvelope_sum : (∑ a ∈ W.tailCertificate.support \ W.tailCertificate.finitePrefix, envelope' a) ≤ tailBound')
  (hν : HasCriticalNu M correlationLength W.certificate.predictedExponent) :
-- imply
  HasCriticalNu M correlationLength (W.with_tailEnvelope_and_tailBudget envelope' henvelope_nonneg hweight_le henvelope_sum).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_tailEnvelope_and_tailBudget_hasCriticalNu W envelope' henvelope_nonneg hweight_le henvelope_sum hν

/--
[with_larger_tailBudget_tailBudget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBudget_tailBudget_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  (W.with_larger_tailBudget hle).tailBudget = tailBound' := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_larger_tailBudget_tailBudget W hle

/--
[with_larger_tailBudget_tailPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBudget_tailPrefixSum_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  (W.with_larger_tailBudget hle).tailPrefixSum = W.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_larger_tailBudget_tailPrefixSum W hle

/--
[with_larger_tailBudget_tailCertifiedTotalBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBudget_tailCertifiedTotalBound_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  (W.with_larger_tailBudget hle).tailCertifiedTotalBound = W.tailPrefixSum + tailBound' := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_larger_tailBudget_tailCertifiedTotalBound W hle

/--
[with_larger_tailBudget_tailContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBudget_tailContribution_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  (W.with_larger_tailBudget hle).tailContribution = W.tailContribution := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_larger_tailBudget_tailContribution W hle

/--
[with_larger_tailBudget_tailTotalTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBudget_tailTotalTsum_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  (W.with_larger_tailBudget hle).tailTotalTsum = W.tailTotalTsum := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_larger_tailBudget_tailTotalTsum W hle

/--
[with_larger_tailBudget_tailSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBudget_tailSupport_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  (W.with_larger_tailBudget hle).tailSupport = W.tailSupport := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_larger_tailBudget_tailSupport W hle

/--
[with_larger_tailBudget_tailRemainderSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBudget_tailRemainderSum_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  (W.with_larger_tailBudget hle).tailRemainderSum = W.tailRemainderSum := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_larger_tailBudget_tailRemainderSum W hle

/--
[with_larger_tailBudget_tailEnvelopeSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBudget_tailEnvelopeSum_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  (W.with_larger_tailBudget hle).tailEnvelopeSum = W.tailEnvelopeSum := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_larger_tailBudget_tailEnvelopeSum W hle

/--
[with_larger_tailBudget_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBudget_certificate_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  (W.with_larger_tailBudget hle).certificate = W.certificate := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_larger_tailBudget_certificate W hle

/--
[with_larger_tailBudget_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBudget_rgToExponentBridge_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound')
  (hbridge : W.certificate.RGToExponentBridge correlationLength) :
-- imply
  (W.with_larger_tailBudget hle).certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_larger_tailBudget_rgToExponentBridge W hle hbridge

/--
[with_larger_tailBudget_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBudget_valid_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound')
  (hvalid : W.certificate.Valid correlationLength) :
-- imply
  (W.with_larger_tailBudget hle).certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_larger_tailBudget_valid W hle hvalid

/--
[with_larger_tailBudget_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma with_larger_tailBudget_hasCriticalNu_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound')
  (hν : HasCriticalNu M correlationLength W.certificate.predictedExponent) :
-- imply
  HasCriticalNu M correlationLength (W.with_larger_tailBudget hle).certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.with_larger_tailBudget_hasCriticalNu W hle hν

/--
[tail_tsum_le_prefix_add_of_tailBudget_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tail_tsum_le_prefix_add_of_tailBudget_le_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  (∑' a, W.tailCertificate.weight a) ≤ W.tailPrefixSum + tailBound' := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tail_tsum_le_prefix_add_of_tailBudget_le W hle

/--
[tailTotalTsum_le_prefix_add_of_tailBudget_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tailTotalTsum_le_prefix_add_of_tailBudget_le_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  W.tailTotalTsum ≤ W.tailPrefixSum + tailBound' := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tailTotalTsum_le_prefix_add_of_tailBudget_le W hle

/--
[tailRemainderSum_le_of_tailBudget_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tailRemainderSum_le_of_tailBudget_le_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  W.tailRemainderSum ≤ tailBound' := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tailRemainderSum_le_of_tailBudget_le W hle

/--
[tailCertifiedTotalBound_le_prefix_add_of_tailBudget_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tailCertifiedTotalBound_le_prefix_add_of_tailBudget_le_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {tailBound' : ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hle : W.tailBudget ≤ tailBound') :
-- imply
  W.tailCertifiedTotalBound ≤ W.tailPrefixSum + tailBound' := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tailCertifiedTotalBound_le_prefix_add_of_tailBudget_le W hle

/--
[tailPrefixSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tailPrefixSum_nonneg_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  0 ≤ W.tailPrefixSum := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tailPrefixSum_nonneg W

/--
[tailBudget_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tailBudget_nonneg_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  0 ≤ W.tailBudget := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tailBudget_nonneg W

/--
[tailCertifiedTotalBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tailCertifiedTotalBound_nonneg_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  0 ≤ W.tailCertifiedTotalBound := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tailCertifiedTotalBound_nonneg W

/--
[tail_tsum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma tail_tsum_nonneg_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  0 ≤ ∑' a, W.tailCertificate.weight a := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.tail_tsum_nonneg W

/--
[stable_fixedPoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma stable_fixedPoint_mem_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  FiniteContraction.ClosedBall W.stable.contraction.center W.stable.contraction.radius W.stable.fixedPoint := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.stable_fixedPoint_mem W

/--
[stable_exists_unique_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma stable_exists_unique_fixedPoint_eq
  [DecidableEq α]
  {M : CriticalModel ι}
-- given
  (W : FiniteWitnessPackage (α := α) M) :
-- imply
  ∃! p : Fin W.nStable → ℝ, W.stable.map p = p := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.stable_exists_unique_fixedPoint W

/--
[valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma valid_of_bridge_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_bridge W hbridge

/--
[hasCriticalNu_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma hasCriticalNu_of_bridge_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hbridge : W.certificate.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_bridge W hbridge

/--
[rgToExponentBridge_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma rgToExponentBridge_of_bridge_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_bridge_congr_predictedExponent W hpred hbridge

/--
[valid_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma valid_of_bridge_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_bridge_congr_predictedExponent W hpred hbridge

/--
[hasCriticalNu_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma hasCriticalNu_of_bridge_congr_predictedExponent_eq
  [DecidableEq α]
  {M : CriticalModel ι}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hpred : W.certificate.predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength) :
-- imply
  HasCriticalNu M correlationLength W.certificate.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.hasCriticalNu_of_bridge_congr_predictedExponent W hpred hbridge

/--
[rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma rgToExponentBridge_of_hasCriticalNu_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hν : HasCriticalNu M correlationLength W.certificate.predictedExponent) :
-- imply
  W.certificate.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.rgToExponentBridge_of_hasCriticalNu W hν

/--
[valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean)
-/
@[path]
private lemma valid_of_hasCriticalNu_eq_2
  [DecidableEq α]
  {M : CriticalModel ι}
  {correlationLength : ℝ → ℝ}
-- given
  (W : FiniteWitnessPackage (α := α) M)
  (hν : HasCriticalNu M correlationLength W.certificate.predictedExponent) :
-- imply
  W.certificate.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.FiniteWitnessPackage.valid_of_hasCriticalNu W hν


-- created on 2026-10-23
