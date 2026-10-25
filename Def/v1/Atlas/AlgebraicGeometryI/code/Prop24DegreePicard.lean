/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop24DegreePicard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.RingTheory.Polynomial.Quotient
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Prop24DegreePicard
open Polynomial


noncomputable section

namespace Prop24Picard

variable {Y : Type*}

/-- The degree map on Weil divisors: sum of multiplicities. -/
noncomputable def weilDegree : WeilDiv Y →+ ℤ where
  toFun D := D.sum (fun _ n => n)
  map_zero' := by simp [Finsupp.sum]
  map_add' := by
    intro a b
    classical
    exact Finsupp.sum_add_index (by simp) (by intros; rfl)

/-- The degree homomorphism descends from Weil divisors to `Pic(Y) = WeilDiv / P` when
`P` is a subgroup of degree-zero divisors. -/
noncomputable def degPic (P : AddSubgroup (WeilDiv Y))
    (hP : ∀ D ∈ P, weilDegree D = 0) :
    (WeilDiv Y ⧸ P) →+ ℤ :=
  QuotientAddGroup.lift P weilDegree (fun x hx => hP x hx)

end Prop24Picard
end
