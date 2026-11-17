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
public import Instance.v1.Atlas.ArithmeticGeometry.code.PadicNumbers.Part2


public section

/-- Definition 4.18 (discrete valuation): a function $v : R \to \mathbb{Z} \cup \{\infty\}$
satisfying $v(a) = \infty \iff a = 0$, $v(ab) = v(a) + v(b)$, and the ultrametric inequality
$\min(v(a), v(b)) \le v(a + b)$. -/
structure DiscreteValuation (R : Type*) [CommRing R] where
  val : R → WithTop ℤ
  val_eq_top_iff : ∀ a : R, val a = ⊤ ↔ a = 0
  val_mul : ∀ a b : R, val (a * b) = val a + val b
  val_add : ∀ a b : R, min (val a) (val b) ≤ val (a + b)

