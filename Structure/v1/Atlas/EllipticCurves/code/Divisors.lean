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
import Theorem.v1.Atlas.EllipticCurves.code.Divisors.Part2


noncomputable section

open Finsupp

variable {P : Type*}

namespace CurveDiv

/-- A "function-field-with-divisor-map" structure: a multiplicative group `F`
(intended to be the function field `k(C)^×`), a subgroup `kUnits` of constants
`k^×`, and a group homomorphism `divMap : (F, ·) → (Div C, +)` sending each
nonzero function to its principal divisor `div f`. -/
structure FunctionFieldDiv (P : Type*) where
  F : Type*
  [instCommGroup : CommGroup F]
  kUnits : Subgroup F
  divMap : Additive F →+ CurveDiv P

end CurveDiv
end
