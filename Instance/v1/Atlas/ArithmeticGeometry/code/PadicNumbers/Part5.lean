module
public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib
public import Abbrev.v1.Atlas.ArithmeticGeometry.code.PadicNumbers.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace PadicUnits

noncomputable section

variable (p : ℕ) [Fact (Nat.Prime p)]

instance : Group (padicUnits p) := inferInstance

instance : CommGroup (padicUnits p) := inferInstance

end
end PadicUnits
