module
public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib
public import Instance.v1.Atlas.ArithmeticGeometry.code.PadicNumbers.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace PadicInt

open Finset PadicInt

variable {p : ℕ} [hp : Fact p.Prime]

/-- The $n$-th digit in the $p$-adic expansion of $a \in \mathbb{Z}_p$, defined via the
`PadicInt.appr` natural-number approximation. -/
noncomputable def padicDigit (a : ℤ_[p]) (n : ℕ) : ℕ :=
  (a.appr (n + 1) - a.appr n) / p ^ n

end PadicInt
