/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop


noncomputable section

open Finsupp

variable {P : Type*}

/-- The group of divisors on a curve (with point type `P`): the free abelian
group on `P`, modeled as `P →₀ ℤ`. Cf. Definition 23.13 (Sutherland §23.2): a
divisor is a finite formal sum `D = ∑_P n_P [P]` of points with integer
coefficients. -/
abbrev CurveDiv (P : Type*) := P →₀ ℤ

end
