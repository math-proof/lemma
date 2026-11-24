module
public import Def.v1.Atlas.AlgebraicGeometryI.code.CartierDivisorScheme.Part3
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CartierDivisorScheme
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CartierDivisorGroup
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.LocallyFactorialDivisors
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.DivisorsPicard
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.WeilDivisor
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.PicardGroup
public import Def.v1.Atlas.AlgebraicGeometryI.code.CartierDivisorGroup.Part2
public import Def.v1.Atlas.AlgebraicGeometryI.code.LocallyFactorialDivisors.Part7
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.DivisorsPicard.Part3
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.WeilDivisor
public import Instance.v1.Atlas.AlgebraicGeometryI.code.PicardGroup
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.CohomologyPicard
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.Lec14DivisorsPicard.Part3
open AlgebraicGeometry CategoryTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec14DivisorsPicard.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

universe u

namespace Lec14DivisorsPicard

section DivisorDegree

/-- Packaged `AddMonoidHom` version of `weilDivisorDegree`. -/
def degreeHom {Y : Type*} [DecidableEq Y] : WeilDivisor.Group Y →+ ℤ where
  toFun := weilDivisorDegree
  map_zero' := weilDivisorDegree_zero
  map_add' := weilDivisorDegree_add

end DivisorDegree
end Lec14DivisorsPicard
end
