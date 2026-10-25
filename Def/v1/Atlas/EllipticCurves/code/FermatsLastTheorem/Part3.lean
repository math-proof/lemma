/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FermatsLastTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies
import Abbrev.v1.Atlas.EllipticCurves.code.FermatsLastTheorem.Part3


noncomputable section

namespace EllipticCurve

/-- The conductor of an elliptic curve over `ℚ`, re-exported from the `FLT` namespace. -/
def IsSemistable (E : FLT.EllipticCurveOverQ) : Prop := FLT.IsSemistable E

end EllipticCurve
end
