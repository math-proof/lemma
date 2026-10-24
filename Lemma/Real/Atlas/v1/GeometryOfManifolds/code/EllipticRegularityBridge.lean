import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.EllipticRegularityBridge
open EllipticRegularityBridge


namespace EllipticRegularityBridge

/--
[isSmoothForm_iff_contMDiff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EllipticRegularityBridge.lean)
-/
@[path]
lemma isSmoothForm_iff_contMDiff
  {n k : ℕ}
  {ξ : DiffForm n k} :
-- imply
  IsSmoothForm ξ ↔ ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (modelWithCornersSelf ℝ ((EuclideanSpace ℝ (Fin n)) [⋀^Fin k]→L[ℝ] ℝ)) ⊤ ξ :=
-- proof
  contMDiff_iff_contDiff.symm

end EllipticRegularityBridge

namespace EllipticRegularityBridge

/--
[IsSmoothForm.toContMDiff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EllipticRegularityBridge.lean)
-/
@[path]
lemma IsSmoothForm.toContMDiff
  {n k : ℕ}
  {ξ : DiffForm n k}
-- given
  (h : IsSmoothForm ξ) :
-- imply
  ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (modelWithCornersSelf ℝ ((EuclideanSpace ℝ (Fin n)) [⋀^Fin k]→L[ℝ] ℝ)) ⊤ ξ :=
-- proof
  (isSmoothForm_iff_contMDiff ξ).mp h

end EllipticRegularityBridge

namespace EllipticRegularityBridge

/--
[IsSmoothForm.ofContMDiff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EllipticRegularityBridge.lean)
-/
@[path]
lemma IsSmoothForm.ofContMDiff
  {n k : ℕ}
  {ξ : DiffForm n k}
-- given
  (h : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (modelWithCornersSelf ℝ ((EuclideanSpace ℝ (Fin n)) [⋀^Fin k]→L[ℝ] ℝ)) ⊤ ξ) :
-- imply
  IsSmoothForm ξ :=
-- proof
  (isSmoothForm_iff_contMDiff ξ).mpr h
/-- Bridge: $H^0$-Sobolev regularity coincides with membership in $L^2$ under a finite measure. -/

end EllipticRegularityBridge


-- created on 2026-10-23
