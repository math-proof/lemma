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
import Instance.v1.Atlas.ArithmeticGeometry.code.PadicNumbers.Part2


/-- Definition 4.18 (discrete valuation): a function $v : R \to \mathbb{Z} \cup \{\infty\}$
satisfying $v(a) = \infty \iff a = 0$, $v(ab) = v(a) + v(b)$, and the ultrametric inequality
$\min(v(a), v(b)) \le v(a + b)$. -/
structure DiscreteValuation (R : Type*) [CommRing R] where
  val : R → WithTop ℤ
  val_eq_top_iff : ∀ a : R, val a = ⊤ ↔ a = 0
  val_mul : ∀ a b : R, val (a * b) = val a + val b
  val_add : ∀ a b : R, min (val a) (val b) ≤ val (a + b)

