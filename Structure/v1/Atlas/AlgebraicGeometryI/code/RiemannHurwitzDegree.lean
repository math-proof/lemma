/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitzFormula
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannHurwitzFormula
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves.Part2


noncomputable section

open RiemannHurwitzFormula CanonicalSheafCurves

namespace RiemannHurwitzDegree

/-- Bundle of data for a finite cover f : X → Y of smooth complete curves: a
`CurveMorphismData` together with the source and target curves and equalities
identifying the abstract canonical degrees with the curves' canonical degrees. -/
structure CurveCoverData where
  morphism : CurveMorphismData
  source : SmoothCompleteCurve
  target : SmoothCompleteCurve
  h_degK_X : morphism.deg_KX = source.degK
  h_degK_Y : morphism.deg_KY = target.degK

end RiemannHurwitzDegree
end
