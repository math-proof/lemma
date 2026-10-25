/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannRochEulerCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
open RiemannRochCurves CanonicalSheafCurves


noncomputable section

namespace RiemannRochEulerCurves

/-- The Euler characteristic of the structure sheaf is `1 - g`. -/
theorem chi_structure_sheaf_curve (C : SmoothCompleteCurve) :
    C.χ (1, 0) = 1 - C.g :=
  C.hχ_struct

/-- Euler characteristic of the canonical sheaf: `χ(ω_C) = g - 1`. -/
theorem euler_char_canonical (C : SmoothCompleteCurve) :
    C.χ (1, C.degK) = C.g - 1 :=
  chi_canonical C

end RiemannRochEulerCurves
end
