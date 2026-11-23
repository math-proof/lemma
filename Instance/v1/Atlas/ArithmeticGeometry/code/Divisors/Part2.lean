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
public import Structure.v1.Atlas.ArithmeticGeometry.code.Divisors.Part2
@[expose] public section

attribute [instance] ClosedPointRes.residueFieldField ClosedPointRes.residueFieldAlgebra
    ClosedPointRes.finiteDimensional


namespace ClosedPoint

variable {G : Type*} {C : Type*} [Group G] [MulAction G C]

namespace CurveWithOrd

variable {C : Type*} {F : Type*} [Field F] [FunctionFieldCurve C F]

namespace FunctionFieldPlace

variable {F : Type*} [Field F] {k : Type*} [Field k]

instance (P : FunctionFieldPlace F k) : IsPrincipalIdealRing P.valuationSubring :=
  P.isPrincipalIdealRing

instance (P : FunctionFieldPlace F k) : IsFractionRing P.valuationSubring F :=
  inferInstance

end FunctionFieldPlace
end CurveWithOrd
end ClosedPoint
