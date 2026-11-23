/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Def.v1.Atlas.ArithmeticGeometry.code.DegreePullback
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.DegreePullback
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.RationalLineCriterion
public import Def.v1.Atlas.ArithmeticGeometry.code.RationalLineCriterion
public import Theorem.v1.Atlas.ArithmeticGeometry.code.Divisors

@[expose] public section

attribute [instance] ClosedPointRes.residueFieldField ClosedPointRes.residueFieldAlgebra
    ClosedPointRes.finiteDimensional


namespace ClosedPoint

variable {G : Type*} {C : Type*} [Group G] [MulAction G C]

namespace CurveWithOrd

variable {C : Type*} {F : Type*} [Field F] [FunctionFieldCurve C F]

noncomputable def principalDivisor (f : Fˣ) : CurveDivisor C :=
  Finsupp.ofSupportFinite (fun P => ord P f) (ord_finite_support f)

end CurveWithOrd
end ClosedPoint
