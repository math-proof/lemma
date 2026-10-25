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
import Def.v1.Atlas.EllipticCurves.code.Divisors


noncomputable section

open Finsupp

variable {P : Type*}

namespace CurveDiv

/-- The degree of the zero divisor is zero. -/
@[simp]
theorem deg_zero : deg (0 : CurveDiv P) = 0 := by
  simp [deg, Finsupp.sum]

/-- The degree of a single-point divisor `n[p]` is `n`. -/
@[simp]
theorem deg_single [DecidableEq P] (p : P) (n : ℤ) :
    deg (Finsupp.single p n) = n := by
  simp [deg, Finsupp.sum_single_index]

/-- Additivity of the degree: `deg(D₁ + D₂) = deg D₁ + deg D₂`. -/
theorem deg_add (D₁ D₂ : CurveDiv P) :
    (D₁ + D₂).deg = D₁.deg + D₂.deg := by
  classical
  simp only [deg]
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

end CurveDiv
end
