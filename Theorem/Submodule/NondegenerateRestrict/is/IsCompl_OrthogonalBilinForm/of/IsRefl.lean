module

public import Mathlib

public section


/--
[nondegenerate_iff_compl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/NondegenerateThreeWay.lean)
-/
public theorem Submodule.NondegenerateRestrict.is.IsCompl_OrthogonalBilinForm.of.IsRefl
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
-- updated on 2026-10-26
