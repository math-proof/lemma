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
import Class.v1.Atlas.ArithmeticGeometry.code.Divisors.Part2
attribute [instance] ClosedPointRes.residueFieldField ClosedPointRes.residueFieldAlgebra
    ClosedPointRes.finiteDimensional


namespace ClosedPoint

variable {G : Type*} {C : Type*} [Group G] [MulAction G C]

namespace CurveWithOrd

variable {C : Type*} {F : Type*} [Field F] [FunctionFieldCurve C F]

theorem CurveWithConstants.ord_constant {C : Type*} {k : Type*} {F : Type*}
    [Field k] [Field F] [Algebra k F] [inst : CurveWithConstants C k F]
    (P : C) (a : kˣ) :
    CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom a) = 0 := by
  have h_pos : (0 : ℤ) ≤ CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom a) :=
    inst.toFunctionFieldCurve.ord_nonneg_of_coordRingElem _ (inst.const_isCoordRingElem a) P
  have h_neg : (0 : ℤ) ≤ CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom a)⁻¹ :=
    inst.toFunctionFieldCurve.ord_nonneg_of_coordRingElem _ (inst.const_inv_isCoordRingElem a) P
  have h_inv : CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom a)⁻¹ =
    -CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom a) :=
    CurveWithOrd.ord_inv P _
  omega

end CurveWithOrd
end ClosedPoint
