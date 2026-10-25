/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Order.DirectedInverseSystem
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib
import Def.v1.Atlas.ArithmeticGeometry.code.PadicNumbers


namespace InverseLimit

namespace NatInverseSystem

variable (S : NatInverseSystem)

/-- A countable inverse system of commutative rings: a sequence of `CommRing`s with ring
homomorphism transition maps. -/
structure NatRingInverseSystem where
  obj : ℕ → Type*
  [instCommRing : ∀ n, CommRing (obj n)]
  map : ∀ n, obj (n + 1) →+* obj n

end NatInverseSystem
end InverseLimit
