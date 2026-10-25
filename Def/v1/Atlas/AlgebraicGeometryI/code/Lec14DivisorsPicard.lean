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
import Theorem.v1.Atlas.AlgebraicGeometryI.code.Lec14DivisorsPicard.Part2
open AlgebraicGeometry CategoryTheory


noncomputable section

universe u

namespace Lec14DivisorsPicard

section LineBundlesCartier

open InvertibleSheaves

variable (R : Type u) [CommRing R]

/-- Corollary 19 (Lec 14): the Picard group `Pic(R)` of invertible sheaves on `Spec R`
is naturally a commutative group under tensor product. -/
@[reducible]
def corollary_19_invertible_sheaves_group (R : Type*) [CommRing R] :
    CommGroup (CommRing.Pic R) := inferInstance

end LineBundlesCartier

section DivisorDegree

/-- Degree of a Weil divisor `D = Σ nᵢ [Pᵢ]`: the integer sum of the coefficients `Σ nᵢ`. -/
def weilDivisorDegree {Y : Type*} [DecidableEq Y] (D : WeilDivisor.Group Y) : ℤ :=
  D.sum (fun _ n => n)

end DivisorDegree
end Lec14DivisorsPicard
end
