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
import Structure.v1.Atlas.ArithmeticGeometry.code.PadicNumbers.Part2


namespace InverseLimit

namespace NatInverseSystem

variable (S : NatInverseSystem)

attribute [instance] NatRingInverseSystem.instCommRing

namespace NatRingInverseSystem

variable (S : NatRingInverseSystem)

/-- Forget the ring structure on a `NatRingInverseSystem`, viewing it as a `NatInverseSystem`. -/
def toNatInverseSystem : NatInverseSystem where
  obj := S.obj
  map n := S.map n

/-- The inverse limit of a `NatRingInverseSystem` realized as a subring of the product
$\prod_n S_n$, consisting of coherent sequences. -/
def invLimSubring : Subring (∀ n, S.obj n) where
  carrier := { a | ∀ n, S.map n (a (n + 1)) = a n }
  mul_mem' := fun {a b} ha hb n => by
    simp only [Pi.mul_apply, map_mul, ha n, hb n]
  one_mem' := fun n => by
    simp only [Pi.one_apply, map_one]
  add_mem' := fun {a b} ha hb n => by
    simp only [Pi.add_apply, map_add, ha n, hb n]
  zero_mem' := fun n => by
    simp only [Pi.zero_apply, map_zero]
  neg_mem' := fun {a} ha n => by
    simp only [Pi.neg_apply, map_neg, ha n]

end NatRingInverseSystem
end NatInverseSystem
end InverseLimit
