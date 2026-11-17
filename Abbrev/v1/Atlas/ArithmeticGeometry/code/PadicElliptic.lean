/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicElliptic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Monotone.Basic


@[expose] public noncomputable section

open scoped Padic


attribute [local instance] Classical.dec

namespace PadicElliptic

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- The group of $\mathbb{Q}_p$-points of a Weierstrass curve $W$ defined over $\mathbb{Q}$,
obtained by base-changing to $\mathbb{Q}_p$ and taking the affine point set. -/
abbrev PadicPointGroup (W : WeierstrassCurve ℚ) : Type :=
  (W.baseChange ℚ_[p]).toAffine.Point

end PadicElliptic
end
