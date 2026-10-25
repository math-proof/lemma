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
import Abbrev.v1.Atlas.EllipticCurves.code.Divisors


noncomputable section

open Finsupp

variable {P : Type*}

namespace CurveDiv

/-- The divisor `[p]` consisting of a single point with multiplicity `1`. -/
def of (p : P) : CurveDiv P := Finsupp.single p 1

/-- The coefficient (valuation) of `D` at `p`: this is `v_P(D)` in the notation
of Definition 23.13. -/
def coeff (D : CurveDiv P) (p : P) : ℤ := D p

/-- The support of a divisor `D`: the finite set of points where its coefficient
is nonzero. Cf. Definition 23.13. -/
def supp (D : CurveDiv P) : Finset P := D.support

/-- The degree of a divisor: `deg D := ∑_P v_P(D)` (Definition 23.13). -/
def deg (D : CurveDiv P) : ℤ := D.sum (fun _ n => n)

end CurveDiv
end
