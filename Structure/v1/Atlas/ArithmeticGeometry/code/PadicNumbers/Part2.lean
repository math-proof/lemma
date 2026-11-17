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
public import Def.v1.Atlas.ArithmeticGeometry.code.PadicNumbers


public section

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
