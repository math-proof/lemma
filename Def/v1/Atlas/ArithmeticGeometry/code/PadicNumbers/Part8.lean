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
import Theorem.v1.Atlas.ArithmeticGeometry.code.PadicNumbers.Part3


namespace PadicInt

open Finset PadicInt

variable {p : ℕ} [hp : Fact p.Prime]

/-- The $p$-adic expansion of $a \in \mathbb{Z}_p$ as a sequence valued in `Fin p`, packaging
`padicDigit` together with the bound `padicDigit_lt`. -/
noncomputable def padicExpansion (a : ℤ_[p]) (n : ℕ) : Fin p :=
  ⟨padicDigit a n, padicDigit_lt a n⟩

/-- Given a sequence of digits $b : \mathbb{N} \to \mathrm{Fin}\,p$, the partial sum
$\sum_{k<n} b_k\,p^k \in \mathbb{Z}$. -/
noncomputable def digitPartialSum (b : ℕ → Fin p) (n : ℕ) : ℤ :=
  ∑ k ∈ range n, (b k).val * (p : ℤ) ^ k


end PadicInt
