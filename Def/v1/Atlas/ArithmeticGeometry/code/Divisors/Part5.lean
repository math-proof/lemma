module
public import Mathlib
public import Def.v1.Atlas.ArithmeticGeometry.code.DegreePullback
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.DegreePullback
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.RationalLineCriterion
public import Def.v1.Atlas.ArithmeticGeometry.code.RationalLineCriterion
public import Abbrev.v1.Atlas.ArithmeticGeometry.code.Divisors.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

attribute [instance] ClosedPointRes.residueFieldField ClosedPointRes.residueFieldAlgebra
    ClosedPointRes.finiteDimensional


namespace ClosedPoint

variable {G : Type*} {C : Type*} [Group G] [MulAction G C]

namespace RationalDivisor

variable {G : Type*} {C : Type*} [Group G] [MulAction G C]

noncomputable def coeff (D : RationalDivisor G C) (P : ClosedPoint G C) : ℤ := D P

noncomputable def rationalDivisorSupport (D : RationalDivisor G C) :
    Finset (ClosedPoint G C) := D.support

end RationalDivisor
end ClosedPoint
