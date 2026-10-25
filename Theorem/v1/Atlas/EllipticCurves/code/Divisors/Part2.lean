/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Def.v1.Atlas.EllipticCurves.code.Divisors.Part2


noncomputable section

open Finsupp

variable {P : Type*}

namespace CurveDiv

/-- Membership in `DivZero P` is equivalent to having degree zero. -/
theorem mem_divZero_iff (D : CurveDiv P) :
    D ∈ DivZero P ↔ D.deg = 0 := by
  simp [DivZero, degHom, AddMonoidHom.mem_ker]

end CurveDiv
end
