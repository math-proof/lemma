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
import Def.v1.Atlas.ArithmeticGeometry.code.PadicNumbers.Part6


namespace PadicUnits

noncomputable section

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The group of units of $\mathbb{Z}_p$, abbreviated `padicUnits p`. -/
abbrev padicUnits : Type := (ℤ_[p])ˣ

end
end PadicUnits
