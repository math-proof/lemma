/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ArithmeticGeometry.code.DegreePullback
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.DegreePullback
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RationalLineCriterion
import Def.v1.Atlas.ArithmeticGeometry.code.RationalLineCriterion
import Def.v1.Atlas.ArithmeticGeometry.code.Divisors.Part6
attribute [instance] ClosedPointRes.residueFieldField ClosedPointRes.residueFieldAlgebra
    ClosedPointRes.finiteDimensional


namespace ClosedPoint

variable {G : Type*} {C : Type*} [Group G] [MulAction G C]

namespace CurveWithOrd

variable {C : Type*} {F : Type*} [Field F] [FunctionFieldCurve C F]

@[simp]
theorem principalDivisor_apply (f : Fˣ) (P : C) :
    (principalDivisor f : CurveDivisor C) P = ord P f := by
  simp [principalDivisor, Finsupp.ofSupportFinite]

@[simp]
theorem principalDivisor_one : principalDivisor (C := C) (F := F) (1 : Fˣ) = 0 := by
  ext P
  simp [ord_one]

theorem principalDivisor_mul (f g : Fˣ) :
    principalDivisor (C := C) (f * g) = principalDivisor f + principalDivisor g := by
  ext P
  simp [ord_mul]

theorem principalDivisor_inv (f : Fˣ) :
    principalDivisor (C := C) f⁻¹ = -principalDivisor f := by
  ext P
  simp [ord_inv]

end CurveWithOrd
end ClosedPoint
