/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalSheafCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.CoherentSheavesCurves.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CoherentSheavesCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalBundleProjective
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalBundleGeneral
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochCurves
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleProjective.Part4
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleGeneral
import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannRochCurves
import Structure.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves
set_option maxHeartbeats 800000

open RiemannRochCurves


noncomputable section

namespace CanonicalSheafCurves

/-- Serre duality at the level of Euler characteristics: `χ(K_C) = g - 1`. -/
def canonicalSheafClass (C : SmoothCompleteCurve) : ℤ × ℤ := (1, C.degK)

/-- Genus of the smooth complete curve `C`, as an integer. -/
def curveGenusOfSmooth (C : SmoothCompleteCurve) : ℤ := C.g

/-- Degree of the canonical divisor of `C`. -/
def canonicalDeg (C : SmoothCompleteCurve) : ℤ := C.degK

end CanonicalSheafCurves
end
