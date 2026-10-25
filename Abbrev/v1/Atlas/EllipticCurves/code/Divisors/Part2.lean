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
import Def.v1.Atlas.EllipticCurves.code.Divisors.Part3


noncomputable section

open Finsupp

variable {P : Type*}

namespace CurveDiv

attribute [instance] FunctionFieldDiv.instCommGroup

variable (Φ : FunctionFieldDiv P)

/-- Principal divisors are divisors of degree zero. -/
abbrev PicardGroup : Type _ :=
  CurveDiv P ⧸ PrincDiv Φ

/-- Since principal divisors have degree zero, the degree map descends to a
homomorphism `Pic C → ℤ` from the Picard group. -/
abbrev PicardGroupZero : Type _ :=
  (DivZero P) ⧸ (PrincDiv Φ).addSubgroupOf (DivZero P)

end CurveDiv
end
