/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Conics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.HasseMinkowski
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HasseMinkowski
import Mathlib
import Theorem.v1.Atlas.ArithmeticGeometry.code.Conics
variable [Invertible (2 : K)]


section Theorem23

variable {K : Type*} [Field K]

/-- The bilinear pairing $\langle (x_0, y_0, z_0), (x, y, z) \rangle = a x_0 x + b y_0 y + c z_0 z$ associated to the diagonal conic; encodes the polarization of the quadratic form. -/
def bilinScalar (a b c x₀ y₀ z₀ x y z : K) : K :=
  a * x₀ * x + b * y₀ * y + c * z₀ * z

end Theorem23
