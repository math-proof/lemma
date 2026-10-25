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

end GenusConstruction
end
