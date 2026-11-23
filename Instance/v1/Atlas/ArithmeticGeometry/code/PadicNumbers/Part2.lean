/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib
public import Def.v1.Atlas.ArithmeticGeometry.code.PadicNumbers.Part3
@[expose] public section

namespace InverseLimit

namespace NatInverseSystem

variable (S : NatInverseSystem)

attribute [instance] NatRingInverseSystem.instCommRing

section ZModSystem

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] :
    CommRing (zmodRingInverseSystem p).InverseLimitRing :=
  inferInstance

end ZModSystem
end NatInverseSystem
end InverseLimit
