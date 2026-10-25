/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.TateShafarevich.Part2
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.TateShafarevich
import Def.v1.Atlas.ArithmeticGeometry.code.JInvariant.Part2


noncomputable section

universe u

open WeierstrassCurve

namespace shortWeierstrassCurve

variable {R : Type*} [CommRing R] (a₄ a₆ : R)

/-- An elliptic curve bundles an `IsElliptic` instance on its underlying
Weierstrass curve, registered for typeclass search. -/
instance EllipticCurveOver.instIsElliptic {k : Type*} [Field k] (E : EllipticCurveOver k) :
    E.curve.IsElliptic := E.isElliptic

end shortWeierstrassCurve
end
