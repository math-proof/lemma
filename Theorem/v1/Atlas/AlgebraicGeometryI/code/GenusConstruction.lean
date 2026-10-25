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
import Def.v1.Atlas.AlgebraicGeometryI.code.GenusConstruction
open RiemannRochCurves CanonicalSheafCurves CohomologyP1 RiemannRoch


noncomputable section

namespace GenusConstruction

/-- The canonical degree of `P1CurveFromCech k` is `-2`. -/
theorem P1CurveFromCech_degK (k : Type) [Field k] :
    (P1CurveFromCech k).degK = -2 := rfl


end GenusConstruction
end
