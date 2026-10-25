/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/JInvariantDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Tactic


namespace JInvariant

variable {k : Type*} [Field k]

/-- The short Weierstrass curve $y^2 = x^3 + Ax + B$ given by setting $a_1 = a_2 = a_3 = 0$,
$a_4 = A$, $a_6 = B$. -/
def shortWeierstrassCurve (A B : k) : WeierstrassCurve k :=
  ⟨0, 0, 0, A, B⟩

/-- Definition 13.11. The $j$-invariant of the short Weierstrass curve $y^2 = x^3 + Ax + B$:
$j(A, B) = 1728 \cdot 4A^3 / (4A^3 + 27B^2)$. -/
def jInvariant (A B : k) : k :=
  1728 * (4 * A ^ 3) / (4 * A ^ 3 + 27 * B ^ 2)

end JInvariant
