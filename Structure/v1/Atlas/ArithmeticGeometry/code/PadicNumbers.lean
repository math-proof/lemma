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


namespace InverseLimit

/-- A countable inverse system: a sequence of types `obj n` together with transition maps
`map n : obj (n + 1) → obj n`. -/
structure NatInverseSystem where
  obj : ℕ → Type*
  map : ∀ n, obj (n + 1) → obj n

end InverseLimit
