module
public import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves.Part2
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CohomologyP1
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRoch
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochCurves
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.TateCechInfra
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.DedekindCurve
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.CohomologyP1.Part2
public import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRoch
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannRochCurves
public import Def.v1.Atlas.AlgebraicGeometryI.code.TateCechInfra.Part2
public import Def.v1.Atlas.AlgebraicGeometryI.code.DedekindCurve
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.GenusConstruction
open RiemannRochCurves CanonicalSheafCurves CohomologyP1 RiemannRoch


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusConstruction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace GenusConstruction

/-- A smooth complete curve constructed from a finite-dimensional Dedekind algebra `A` over `k`:
genus is the curve genus of `A`, canonical degree is `2g - 2`, and Euler characteristic is the
Riemann-Roch homomorphism. -/
def curveFromDedekind (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] :
    SmoothCompleteCurve where
  g := curveGenus k A
  χ := rrHom (curveGenus k A)
  degK := 2 * (curveGenus k A : ℤ) - 2
  hg_nonneg := Int.natCast_nonneg (curveGenus k A)
  hχ_struct := rr_value_structure_sheaf (curveGenus k A)
  hχ_sky := rr_value_skyscraper (curveGenus k A)
  hwf := curveWitness_of_nat (curveGenus k A)

end GenusConstruction
end
