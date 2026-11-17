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
public import Structure.v1.Atlas.ArithmeticGeometry.code.PadicNumbers.Part3

@[expose] public section

namespace DiscreteValuation

variable {R : Type*} [CommRing R] (v : DiscreteValuation R)

instance : CoeFun (DiscreteValuation R) (fun _ => R → WithTop ℤ) where
  coe v := v.val

end DiscreteValuation
