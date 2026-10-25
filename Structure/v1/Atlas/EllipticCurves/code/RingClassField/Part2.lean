/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/RingClassField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.EllipticCurves.code.PointCounting.Part2
import Lemma.Complex.Atlas.v1.EllipticCurves.code.PointCounting
import Lemma.Complex.Atlas.v1.EllipticCurves.code.OrdinarySupersingular
import Lemma.Complex.Atlas.v1.EllipticCurves.code.HilbertClassPolynomial
import Lemma.Complex.Atlas.v1.EllipticCurves.code.CMTorsor
import Def.v1.Atlas.EllipticCurves.code.OrdinarySupersingular
import Def.v1.Atlas.EllipticCurves.code.HilbertClassPolynomial.Part2
import Def.v1.Atlas.EllipticCurves.code.CMTorsor.Part7
import Def.v1.Atlas.EllipticCurves.code.RingClassField.Part2
open NumberField


noncomputable section

namespace RingClassField

/-- Predicate (in `Prop`) form of "`D` is the discriminant of an imaginary
quadratic order": `D < 0` and `D ≡ 0` or `1 mod 4`. -/
structure IsImagQuadDisc (D : ℤ) : Prop where
  neg : D < 0
  cong : D % 4 = 0 ∨ D % 4 = 1

end RingClassField
end
