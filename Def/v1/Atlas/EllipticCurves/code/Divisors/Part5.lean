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
import Structure.v1.Atlas.EllipticCurves.code.Divisors.Part2


noncomputable section

open Finsupp

variable {P : Type*}

noncomputable section

attribute [instance] SmoothProjectiveCurve.fieldInst

/-- A rational map is *defined at* a point `P` if there exists a rescaling
`c ∈ k(C)^×` so that every coordinate `c · coords i` has nonnegative valuation
at `P` and at least one has valuation zero. -/
def RationalMap.isDefinedAt {C : SmoothProjectiveCurve} {m : ℕ}
    (φ : RationalMap C m) (P : C.Point) : Prop :=
  ∃ (c : C.FunctionField), c ≠ 0 ∧
    (∀ i, (0 : WithTop ℤ) ≤ C.val P (c * φ.coords i)) ∧
    (∃ i, C.val P (c * φ.coords i) = 0)

/-- A rational map is a *morphism* if it is defined at every point. -/
def RationalMap.isMorphism {C : SmoothProjectiveCurve} {m : ℕ}
    (φ : RationalMap C m) : Prop :=
  ∀ P : C.Point, φ.isDefinedAt P

end
end
