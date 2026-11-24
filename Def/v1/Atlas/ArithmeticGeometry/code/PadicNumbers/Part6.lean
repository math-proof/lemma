module
public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib
public import Instance.v1.Atlas.ArithmeticGeometry.code.PadicNumbers.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace DiscreteValuation

variable {R : Type*} [CommRing R] (v : DiscreteValuation R)

/-- Reducible alias for the commutative ring structure on $\mathbb{Z}_p$. -/
@[reducible] def padicInt_commRing : CommRing ℤ_[p] := inferInstance

end DiscreteValuation
