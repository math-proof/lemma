/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CohomologyP1
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRoch
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.TateCechInfra
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.DedekindCurve
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CohomologyP1
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.RiemannRoch
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.RiemannRochCurves
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.TateCechInfra
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.DedekindCurve

open RiemannRochCurves CanonicalSheafCurves CohomologyP1 RiemannRoch

noncomputable section

namespace GenusConstruction


/-- The smooth complete curve `P^1` packaged from Čech data: genus `0`, canonical degree `-2`,
Euler characteristic given by the Riemann-Roch homomorphism. -/
def P1CurveFromCech (_k : Type) [Field _k] : SmoothCompleteCurve where
  g := 0
  χ := rrHom 0
  degK := -2
  hg_nonneg := le_refl 0
  hχ_struct := rr_value_structure_sheaf 0
  hχ_sky := rr_value_skyscraper 0
  hwf := curveWitness_zero

/-- The canonical degree of `P1CurveFromCech k` is `-2`. -/
theorem P1CurveFromCech_degK (k : Type) [Field k] :
    (P1CurveFromCech k).degK = -2 := rfl


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
