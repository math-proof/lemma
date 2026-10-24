import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.Certificate
open StatMech StatMech.Exact3D StatMech.Exact3D.RGCertificate


/--
[predictedExponent_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean)
-/
@[path]
private lemma predictedExponent_pos_eq
  {M : CriticalModel ι}
  {C : RGCertificate M} :
-- imply
  0 < C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.predictedExponent_pos C

/--
[retarget_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean)
-/
@[path]
private lemma retarget_predictedExponent_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {N : CriticalModel κ} :
-- imply
  (C.retarget N).predictedExponent = C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.retarget_predictedExponent C N

/--
[linearizationEnclosure_of_thermal_gt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean)
-/
@[path]
private lemma linearizationEnclosure_of_thermal_gt_one_eq
  {M : CriticalModel ι}
  {C : RGCertificate M} :
-- imply
  C.LinearizationEnclosure := by
-- proof
  apply StatMech.Exact3D.RGCertificate.linearizationEnclosure_of_thermal_gt_one C

/--
[hyperbolicSplitting_of_thermal_gt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean)
-/
@[path]
private lemma hyperbolicSplitting_of_thermal_gt_one_eq
  {M : CriticalModel ι}
  {C : RGCertificate M} :
-- imply
  C.HyperbolicSplitting := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hyperbolicSplitting_of_thermal_gt_one C

/--
[rgToExponentBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean)
-/
@[path]
private lemma rgToExponentBridge_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : D.RGToExponentBridge correlationLength)
  (hpred : C.predictedExponent = D.predictedExponent) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_congr_predictedExponent hbridge hpred

/--
[rgToExponentBridge_congr_predictedExponent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean)
-/
@[path]
private lemma rgToExponentBridge_congr_predictedExponent_iff_eq
  {M : CriticalModel ι}
  {C D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent) :
-- imply
  C.RGToExponentBridge correlationLength ↔ D.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_congr_predictedExponent_iff hpred

/--
[retarget_rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean)
-/
@[path]
private lemma retarget_rgToExponentBridge_of_hasCriticalNu_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu N correlationLength C.predictedExponent) :
-- imply
  (C.retarget N).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.retarget_rgToExponentBridge_of_hasCriticalNu C correlationLength hν

/--
[hasCriticalNu_of_checks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean)
-/
@[path]
private lemma hasCriticalNu_of_checks_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (_hfinite : FiniteCaseChecks C)
  (_htail : TailBounds C)
  (_hfixed : FixedPointEnclosure C)
  (_hlinear : LinearizationEnclosure C)
  (_hhyperbolic : HyperbolicSplitting C)
  (_horbit : OrbitEntry C)
  (hbridge : RGToExponentBridge C correlationLength) :
-- imply
  HasCriticalNu M correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.hasCriticalNu_of_checks C correlationLength _hfinite _htail _hfixed _hlinear _hhyperbolic _horbit hbridge

/--
[valid_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean)
-/
@[path]
private lemma valid_of_bridge_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hfinite : FiniteCaseChecks C)
  (htail : TailBounds C)
  (hfixed : FixedPointEnclosure C)
  (hlinear : LinearizationEnclosure C)
  (hhyperbolic : HyperbolicSplitting C)
  (horbit : OrbitEntry C)
  (hbridge : RGToExponentBridge C correlationLength) :
-- imply
  C.Valid correlationLength where finiteCaseChecks := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_bridge C correlationLength hfinite htail hfixed hlinear hhyperbolic horbit hbridge

/--
[valid_of_bridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean)
-/
@[path]
private lemma valid_of_bridge_congr_predictedExponent_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {D : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hfinite : FiniteCaseChecks C)
  (htail : TailBounds C)
  (hfixed : FixedPointEnclosure C)
  (hlinear : LinearizationEnclosure C)
  (hhyperbolic : HyperbolicSplitting C)
  (horbit : OrbitEntry C)
  (hpred : C.predictedExponent = D.predictedExponent)
  (hbridge : D.RGToExponentBridge correlationLength) :
-- imply
  C.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_bridge_congr_predictedExponent C correlationLength hfinite htail hfixed hlinear hhyperbolic horbit hpred hbridge

/--
[bridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean)
-/
@[path]
private lemma bridge_of_hasCriticalNu_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu M correlationLength C.predictedExponent) :
-- imply
  RGToExponentBridge C correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.bridge_of_hasCriticalNu C correlationLength hν

/--
[valid_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean)
-/
@[path]
private lemma valid_of_hasCriticalNu_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hfinite : FiniteCaseChecks C)
  (htail : TailBounds C)
  (hfixed : FixedPointEnclosure C)
  (hlinear : LinearizationEnclosure C)
  (hhyperbolic : HyperbolicSplitting C)
  (horbit : OrbitEntry C)
  (hν : HasCriticalNu M correlationLength C.predictedExponent) :
-- imply
  C.Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.valid_of_hasCriticalNu C correlationLength hfinite htail hfixed hlinear hhyperbolic horbit hν

/--
[Valid.hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean)
-/
@[path]
private lemma hasCriticalNu_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hC : C.Valid correlationLength) :
-- imply
  HasCriticalNu M correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.Valid.hasCriticalNu hC

/--
[rgToExponentBridge_congr_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean)
-/
@[path]
private lemma rgToExponentBridge_congr_eventually_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
-- given
  (hbridge : C.RGToExponentBridge correlationLength)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength β) :
-- imply
  C.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_congr_eventually hbridge hEq

/--
[rgToExponentBridge_congr_eventually_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean)
-/
@[path]
private lemma rgToExponentBridge_congr_eventually_iff_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
-- given
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength β) :
-- imply
  C.RGToExponentBridge correlationLength ↔ C.RGToExponentBridge comparisonLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_congr_eventually_iff hEq

/--
[retarget_rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean)
-/
@[path]
private lemma retarget_rgToExponentBridge_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hbridge : C.RGToExponentBridge correlationLength)
  (hβc : M.betaC = N.betaC) :
-- imply
  (C.retarget N).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.retarget_rgToExponentBridge hbridge hβc

/--
[retarget_rgToExponentBridge_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean)
-/
@[path]
private lemma retarget_rgToExponentBridge_iff_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hβc : M.betaC = N.betaC) :
-- imply
  C.RGToExponentBridge correlationLength ↔ (C.retarget N).RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.retarget_rgToExponentBridge_iff hβc

/--
[retarget_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean)
-/
@[path]
private lemma retarget_hasCriticalNu_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu M correlationLength C.predictedExponent)
  (hβc : M.betaC = N.betaC) :
-- imply
  HasCriticalNu N correlationLength (C.retarget N).predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.retarget_hasCriticalNu hν hβc

/--
[retarget_hasCriticalNu_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean)
-/
@[path]
private lemma retarget_hasCriticalNu_iff_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hβc : M.betaC = N.betaC) :
-- imply
  HasCriticalNu M correlationLength C.predictedExponent ↔ HasCriticalNu N correlationLength (C.retarget N).predictedExponent := by
-- proof
  apply StatMech.Exact3D.RGCertificate.retarget_hasCriticalNu_iff hβc

/--
[Valid.congr_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean)
-/
@[path]
private lemma congr_eventually_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
-- given
  (hC : C.Valid correlationLength)
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength β) :
-- imply
  C.Valid comparisonLength where finiteCaseChecks := by
-- proof
  apply StatMech.Exact3D.RGCertificate.Valid.congr_eventually hC hEq

/--
[Valid.congr_eventually_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean)
-/
@[path]
private lemma congr_eventually_iff_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength comparisonLength : ℝ → ℝ}
-- given
  (hEq : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), comparisonLength β = correlationLength β) :
-- imply
  C.Valid correlationLength ↔ C.Valid comparisonLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.Valid.congr_eventually_iff hEq

/--
[Valid.retarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean)
-/
@[path]
private lemma retarget_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hC : C.Valid correlationLength)
  (hβc : M.betaC = N.betaC) :
-- imply
  (C.retarget N).Valid correlationLength where finiteCaseChecks := by
-- proof
  apply StatMech.Exact3D.RGCertificate.Valid.retarget hC hβc

/--
[Valid.retarget_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Certificate.lean)
-/
@[path]
private lemma retarget_iff_eq
  {M : CriticalModel ι}
  {N : CriticalModel κ}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hβc : M.betaC = N.betaC) :
-- imply
  C.Valid correlationLength ↔ (C.retarget N).Valid correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.Valid.retarget_iff hβc


-- created on 2026-10-23
