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
import Instance.v1.Atlas.EllipticCurves.code.FermatsLastTheorem


noncomputable section

namespace EllipticCurve

/-- Convenience abbreviation for `FLT.EllipticCurveOverQ`, the type of elliptic
curves over `ℚ`. -/
abbrev OverQ := FLT.EllipticCurveOverQ

end EllipticCurve
end
