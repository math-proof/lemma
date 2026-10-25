import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.RGBridgeCriteria
open StatMech StatMech.Exact3D StatMech.Exact3D.RGCertificate


/--
[rgToExponentBridge_of_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RGBridgeCriteria.lean)
-/
@[path]
private lemma rgToExponentBridge_of_hasCriticalNu_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hν : HasCriticalNu M correlationLength C.predictedExponent) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_hasCriticalNu C correlationLength hν

/--
[rgToExponentBridge_of_eventually_exact_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RGBridgeCriteria.lean)
-/
@[path]
private lemma rgToExponentBridge_of_eventually_exact_power_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
-- given
  (hξ : ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), correlationLength β = Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_eventually_exact_power C correlationLength hξ

/--
[rgToExponentBridge_of_exact_power_on_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RGBridgeCriteria.lean)
-/
@[path]
private lemma rgToExponentBridge_of_exact_power_on_Ioo_eq
  {M : CriticalModel ι}
  {C : RGCertificate M}
  {correlationLength : ℝ → ℝ}
  {δ : ℝ}
-- given
  (hδ : 0 < δ)
  (hξ : ∀ β, β ∈ Set.Ioo (M.betaC - δ) M.betaC → correlationLength β = Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
-- imply
  C.RGToExponentBridge correlationLength := by
-- proof
  apply StatMech.Exact3D.RGCertificate.rgToExponentBridge_of_exact_power_on_Ioo C correlationLength δ hδ hξ


-- created on 2026-10-23
