import Mathlib
import sympy.Basic


/--
[nondegenerate_iff_compl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/NondegenerateThreeWay.lean)
-/
@[path]
private lemma main
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {B : LinearMap.BilinForm k V}
  {U : Submodule k V}
-- given
  (hBrefl : B.IsRefl) :
-- imply
  (B.restrict U).Nondegenerate ↔ IsCompl U (LinearMap.BilinForm.orthogonal B U) := by
-- proof
  apply B.restrict_nondegenerate_iff_isCompl_orthogonal hBrefl


-- created on 2026-10-23
-- updated on 2026-10-24
