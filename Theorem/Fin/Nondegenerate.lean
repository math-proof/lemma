module

public import Mathlib
public import Def.v1.Atlas.Buildings.code.GeometricAlgebra.HyperbolicCancellation
public import Theorem.Int.OrthogonalSum.eq.Add

public section

open FiniteDimensional Module


/--
[IsNondegenerate'_to_Nondegenerate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/LagrangianFinrank.lean)
-/
public theorem IsNondegenerate'_to_Nondegenerate
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
