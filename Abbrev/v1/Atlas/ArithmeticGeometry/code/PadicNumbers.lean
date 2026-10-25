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
import Def.v1.Atlas.ArithmeticGeometry.code.PadicNumbers.Part2


namespace InverseLimit

namespace NatInverseSystem

variable (S : NatInverseSystem)

attribute [instance] NatRingInverseSystem.instCommRing

namespace NatRingInverseSystem

variable (S : NatRingInverseSystem)

/-- The inverse limit of a `NatRingInverseSystem` as a commutative ring (alias for the subring
`invLimSubring`). -/
abbrev InverseLimitRing : Type _ := S.invLimSubring

end NatRingInverseSystem
end NatInverseSystem
end InverseLimit
