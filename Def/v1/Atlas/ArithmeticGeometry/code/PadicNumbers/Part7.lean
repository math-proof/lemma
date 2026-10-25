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
import Instance.v1.Atlas.ArithmeticGeometry.code.PadicNumbers.Part5


namespace PadicInt

open Finset PadicInt

variable {p : ℕ} [hp : Fact p.Prime]

/-- The $n$-th digit in the $p$-adic expansion of $a \in \mathbb{Z}_p$, defined via the
`PadicInt.appr` natural-number approximation. -/
noncomputable def padicDigit (a : ℤ_[p]) (n : ℕ) : ℕ :=
  (a.appr (n + 1) - a.appr n) / p ^ n

end PadicInt
