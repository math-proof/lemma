import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.GeometricAlgebra.HyperbolicCancellation
import Lemma.Int.OrthogonalSum.eq.Add
open FiniteDimensional Module


/--
[IsNondegenerate'_to_Nondegenerate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/LagrangianFinrank.lean)
-/
@[path]
lemma IsNondegenerate'_to_Nondegenerate
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {B : LinearMap.BilinForm k V}
-- given
  (h : Garrett.BilinForm.IsNondegenerate' B) :
-- imply
  B.Nondegenerate :=
-- proof
  Garrett.IsNondegenerate'_to_Nondegenerate_inline h


-- created on 2026-10-23
