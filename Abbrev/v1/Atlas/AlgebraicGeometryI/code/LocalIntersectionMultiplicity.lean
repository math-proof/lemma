/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LocalIntersectionMultiplicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
set_option maxHeartbeats 400000


noncomputable section

open MvPolynomial Module

namespace LocalIntersection

variable (k : Type*) [Field k]

/-- The quotient ring `k[x,y]/(f,g)` used to define intersection multiplicities. -/
abbrev IntersectionQuotient (f g : MvPolynomial (Fin 2) k) :=
  MvPolynomial (Fin 2) k ⧸ Ideal.span ({f, g} : Set (MvPolynomial (Fin 2) k))

end LocalIntersection
end
