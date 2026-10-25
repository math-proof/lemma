/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CohomologyP1
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRoch
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.TateCechInfra
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.DedekindCurve
import Theorem.v1.Atlas.AlgebraicGeometryI.code.CohomologyP1.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRoch
import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannRochCurves
import Def.v1.Atlas.AlgebraicGeometryI.code.TateCechInfra.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.DedekindCurve
import Theorem.v1.Atlas.AlgebraicGeometryI.code.GenusConstruction
open RiemannRochCurves CanonicalSheafCurves CohomologyP1 RiemannRoch


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
