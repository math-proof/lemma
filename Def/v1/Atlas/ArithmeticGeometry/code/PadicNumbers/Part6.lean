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
import Instance.v1.Atlas.ArithmeticGeometry.code.PadicNumbers.Part4


namespace DiscreteValuation

variable {R : Type*} [CommRing R] (v : DiscreteValuation R)

/-- Reducible alias for the commutative ring structure on $\mathbb{Z}_p$. -/
@[reducible] def padicInt_commRing : CommRing ℤ_[p] := inferInstance

end DiscreteValuation
