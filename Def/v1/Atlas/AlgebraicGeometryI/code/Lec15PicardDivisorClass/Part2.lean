module
public import Def.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part7
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.PicardProjective
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.DivisorsPicard
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.PrincipalDivisorDegree
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.BezoutTheorem
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.LinearEquivDivisors
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.PowerSeriesUFD
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.PicardGroup
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.SmoothCurveDivisors
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.DivisorsPicard.Part3
public import Def.v1.Atlas.AlgebraicGeometryI.code.PrincipalDivisorDegree.Part2
public import Def.v1.Atlas.AlgebraicGeometryI.code.BezoutTheorem
public import Def.v1.Atlas.AlgebraicGeometryI.code.LinearEquivDivisors.Part3
public import Instance.v1.Atlas.AlgebraicGeometryI.code.PowerSeriesUFD
public import Instance.v1.Atlas.AlgebraicGeometryI.code.PicardGroup
public import Def.v1.Atlas.AlgebraicGeometryI.code.SmoothCurveDivisors.Part2
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec15PicardDivisorClass
set_option maxHeartbeats 1600000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec15PicardDivisorClass.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace Lec15PicardDivisorClass

open Module Polynomial LinearEquivDivisors


/-- Dimension `ℓ(D)` of a linear system: the `k`-vector space dimension of `V`. -/
def lD_dim (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V] : ℕ :=
  Module.finrank k V


end Lec15PicardDivisorClass
end
