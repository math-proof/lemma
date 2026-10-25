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
open AlgebraicGeometry CategoryTheory


noncomputable section

universe u

namespace Lec14DivisorsPicard

/-- Cartier divisor group `DC(X)` of an integral scheme `X` (Def 30, Lec 14):
abbreviation for `CartierDivisorScheme.CartierDivisorGroupScheme X`. -/
abbrev cartierDivisorGroupScheme (X : Scheme.{u}) [IsIntegral X] :=
  CartierDivisorScheme.CartierDivisorGroupScheme X

end Lec14DivisorsPicard
end
