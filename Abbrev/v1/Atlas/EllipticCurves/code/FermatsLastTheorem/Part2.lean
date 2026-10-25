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
import Def.v1.Atlas.EllipticCurves.code.FermatsLastTheorem


noncomputable section

namespace FLT

/-- An elliptic curve over `ℚ`: a Weierstrass curve in affine form together with a
proof that it satisfies the elliptic (nonsingular) condition. -/
abbrev EllipticCurveOverQ := { E : WeierstrassCurve.Affine ℚ // E.IsElliptic }

end FLT
end
