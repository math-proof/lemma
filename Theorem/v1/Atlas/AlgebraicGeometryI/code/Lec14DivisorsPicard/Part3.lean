/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec14DivisorsPicard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.CartierDivisorScheme.Part3
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CartierDivisorScheme
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CartierDivisorGroup
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.LocallyFactorialDivisors
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.DivisorsPicard
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.WeilDivisor
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.PicardGroup
import Def.v1.Atlas.AlgebraicGeometryI.code.CartierDivisorGroup.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.LocallyFactorialDivisors.Part7
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.DivisorsPicard.Part3
import Theorem.v1.Atlas.AlgebraicGeometryI.code.WeilDivisor
import Instance.v1.Atlas.AlgebraicGeometryI.code.PicardGroup
import Theorem.v1.Atlas.AlgebraicGeometryI.code.CohomologyPicard
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec14DivisorsPicard
open AlgebraicGeometry CategoryTheory


noncomputable section

universe u

namespace Lec14DivisorsPicard

section DivisorDegree

/-- The degree of the zero divisor is `0`. -/
theorem weilDivisorDegree_zero {Y : Type*} [DecidableEq Y] :
    weilDivisorDegree (0 : WeilDivisor.Group Y) = 0 := by
  simp [weilDivisorDegree, Finsupp.sum]

/-- The degree map is additive: `deg(D₁ + D₂) = deg(D₁) + deg(D₂)`. -/
theorem weilDivisorDegree_add {Y : Type*} [DecidableEq Y] (D₁ D₂ : WeilDivisor.Group Y) :
    weilDivisorDegree (D₁ + D₂) = weilDivisorDegree D₁ + weilDivisorDegree D₂ := by
  simp only [weilDivisorDegree]
  rw [Finsupp.sum_add_index (by simp) (by intros; ring)]

end DivisorDegree
end Lec14DivisorsPicard
end
