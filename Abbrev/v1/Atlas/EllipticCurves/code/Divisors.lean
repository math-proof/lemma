/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop


@[expose] public noncomputable section

open Finsupp

variable {P : Type*}

/-- The group of divisors on a curve (with point type `P`): the free abelian
group on `P`, modeled as `P →₀ ℤ`. Cf. Definition 23.13 (Sutherland §23.2): a
divisor is a finite formal sum `D = ∑_P n_P [P]` of points with integer
coefficients. -/
abbrev CurveDiv (P : Type*) := P →₀ ℤ

end
