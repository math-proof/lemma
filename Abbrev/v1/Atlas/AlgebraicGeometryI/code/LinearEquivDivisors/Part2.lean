/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Def.v1.Atlas.AlgebraicGeometryI.code.LinearEquivDivisors


noncomputable section

open scoped nonZeroDivisors

namespace LinearEquivDivisors

variable {Y : Type*}

/-- The subgroup of principal Weil divisors inside the full Weil divisor group. -/
abbrev PrincipalDivisors (Y : Type*) := AddSubgroup (WeilDivisorGroup Y)

end LinearEquivDivisors
end
