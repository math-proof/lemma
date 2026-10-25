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
import Instance.v1.Atlas.ArithmeticGeometry.code.PadicNumbers


namespace InverseLimit

namespace NatInverseSystem

variable (S : NatInverseSystem)

attribute [instance] NatRingInverseSystem.instCommRing

namespace NatRingInverseSystem

variable (S : NatRingInverseSystem)

/-- The $n$-th projection ring homomorphism `InverseLimitRing →+* S.obj n`. -/
def projRingHom (n : ℕ) : S.InverseLimitRing →+* S.obj n :=
  (Pi.evalRingHom (fun n => S.obj n) n).comp S.invLimSubring.subtype

end NatRingInverseSystem

section ZModSystem

/-- The `NatInverseSystem` whose $n$-th object is $\mathbb{Z}/p^{n+1}\mathbb{Z}$ and whose
transition maps are reduction modulo $p^{n+1}$ to $p^n$. -/
noncomputable def zmodInverseSystem (p : ℕ) [Fact (Nat.Prime p)] : NatInverseSystem where
  obj n := ZMod (p ^ (n + 1))
  map n := ZMod.castHom (pow_dvd_pow p (by omega)) (ZMod (p ^ (n + 1)))

/-- The `NatRingInverseSystem` whose $n$-th object is the commutative ring
$\mathbb{Z}/p^{n+1}\mathbb{Z}$ with reduction ring homomorphisms. -/
noncomputable def zmodRingInverseSystem (p : ℕ) [Fact (Nat.Prime p)] :
    NatRingInverseSystem where
  obj n := ZMod (p ^ (n + 1))
  map n := ZMod.castHom (pow_dvd_pow p (by omega)) (ZMod (p ^ (n + 1)))

end ZModSystem
end NatInverseSystem
end InverseLimit
