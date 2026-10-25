/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/JInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.TateShafarevich.Part2
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.TateShafarevich


noncomputable section

universe u

open WeierstrassCurve

/-- The Weierstrass curve in *short form* $y^2 = x^3 + a_4 x + a_6$, obtained by
setting $a_1 = a_2 = a_3 = 0$. -/
def shortWeierstrassCurve {R : Type*} [CommRing R] (a₄ a₆ : R) : WeierstrassCurve R :=
  ⟨0, 0, 0, a₄, a₆⟩

namespace shortWeierstrassCurve

variable {R : Type*} [CommRing R] (a₄ a₆ : R)

/-- **Definition 26.1.** The $j$-invariant of an elliptic curve $E$ over a field
$k$, extracted from its underlying Weierstrass curve. -/
def EllipticCurveOver.jInvariant {k : Type*} [Field k] (E : EllipticCurveOver k) : k :=
  @WeierstrassCurve.j _ _ E.curve E.isElliptic

end shortWeierstrassCurve
end
