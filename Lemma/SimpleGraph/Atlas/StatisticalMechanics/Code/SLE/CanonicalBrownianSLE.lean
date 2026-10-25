import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.SLE.CanonicalBrownianSLE
open MeasureTheory StatMech StatMech.SLE


/--
[canonicalBrownian_isChordalSLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CanonicalBrownianSLE.lean)
-/
@[path]
private lemma canonicalBrownian_isChordalSLE_eq
  {kappa : Real}
-- given
  (hkappa : 0 <= kappa) :
-- imply
  IsChordalSLE kappa brownianContinuousModification brownianProductLaw (canonicalBrownianLoewnerDomain kappa) (canonicalBrownianLoewnerMaps kappa) := by
-- proof
  apply StatMech.SLE.canonicalBrownian_isChordalSLE kappa hkappa

/--
[canonicalBrownianLoewnerHull_isCompactHull](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CanonicalBrownianSLE.lean)
-/
@[path]
private lemma canonicalBrownianLoewnerHull_isCompactHull_eq
  {kappa : Real} :
-- imply
  ∀ᵐ omega ∂brownianProductLaw, forall t, 0 <= t -> IsCompactHull (canonicalBrownianLoewnerHull kappa omega t) := by
-- proof
  apply StatMech.SLE.canonicalBrownianLoewnerHull_isCompactHull kappa

/--
[canonicalBrownianLoewnerHull_monotoneOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CanonicalBrownianSLE.lean)
-/
@[path]
private lemma canonicalBrownianLoewnerHull_monotoneOn_eq
  {kappa : Real}
-- given
  (omega : Real -> Real) :
-- imply
  MonotoneOn (canonicalBrownianLoewnerHull kappa omega) (Set.Ici 0) := by
-- proof
  apply StatMech.SLE.canonicalBrownianLoewnerHull_monotoneOn kappa omega

/--
[canonicalBrownianLoewnerDomain_eq_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CanonicalBrownianSLE.lean)
-/
@[path]
private lemma canonicalBrownianLoewnerDomain_eq_complement_eq
  {kappa : Real}
  {t : Real}
-- given
  (omega : Real -> Real) :
-- imply
  canonicalBrownianLoewnerDomain kappa omega t = upperHalfPlane \ canonicalBrownianLoewnerHull kappa omega t := by
-- proof
  apply StatMech.SLE.canonicalBrownianLoewnerDomain_eq_complement kappa omega t

/--
[canonicalBrownianLoewnerMaps_conformalOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CanonicalBrownianSLE.lean)
-/
@[path]
private lemma canonicalBrownianLoewnerMaps_conformalOn_eq
  {kappa : Real} :
-- imply
  ∀ᵐ omega ∂brownianProductLaw, forall t, 0 <= t -> forall z, z ∈ canonicalBrownianLoewnerDomain kappa omega t -> ConformalAt (canonicalBrownianLoewnerMaps kappa omega t) z := by
-- proof
  apply StatMech.SLE.canonicalBrownianLoewnerMaps_conformalOn kappa

/--
[canonicalBrownianLoewnerMaps_homeomorph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CanonicalBrownianSLE.lean)
-/
@[path]
private lemma canonicalBrownianLoewnerMaps_homeomorph_eq
  {kappa : Real} :
-- imply
  ∀ᵐ omega ∂brownianProductLaw, ∀ t, 0 <= t -> Nonempty (canonicalBrownianLoewnerDomain kappa omega t ≃ₜ upperHalfPlane) := by
-- proof
  apply StatMech.SLE.canonicalBrownianLoewnerMaps_homeomorph kappa


-- created on 2026-10-23
