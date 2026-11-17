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


public section

namespace InverseLimit

/-- A countable inverse system: a sequence of types `obj n` together with transition maps
`map n : obj (n + 1) → obj n`. -/
structure NatInverseSystem where
  obj : ℕ → Type*
  map : ∀ n, obj (n + 1) → obj n

end InverseLimit
