module
public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib
public import Def.v1.Atlas.ArithmeticGeometry.code.PadicNumbers.Part6


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

/-- The group of units of $\mathbb{Z}_p$, abbreviated `padicUnits p`. -/
abbrev padicUnits : Type := (ℤ_[p])ˣ

end
end PadicUnits
