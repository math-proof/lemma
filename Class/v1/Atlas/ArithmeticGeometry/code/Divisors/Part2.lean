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
import Def.v1.Atlas.ArithmeticGeometry.code.Divisors.Part8
attribute [instance] ClosedPointRes.residueFieldField ClosedPointRes.residueFieldAlgebra
    ClosedPointRes.finiteDimensional


namespace ClosedPoint

variable {G : Type*} {C : Type*} [Group G] [MulAction G C]

namespace CurveWithOrd

variable {C : Type*} {F : Type*} [Field F] [FunctionFieldCurve C F]

class CurveWithConstants (C : Type*) (k : Type*) (F : Type*) [Field k] [Field F]
    [Algebra k F] extends FunctionFieldCurve C F where
  const_isCoordRingElem : ∀ (a : kˣ),
    toFunctionFieldCurve.isCoordRingElem (Units.map (algebraMap k F).toMonoidHom a)
  const_inv_isCoordRingElem : ∀ (a : kˣ),
    toFunctionFieldCurve.isCoordRingElem (Units.map (algebraMap k F).toMonoidHom a)⁻¹
  algClosed_in_extension : ∀ (x : F), IsAlgebraic k x → x ∈ (algebraMap k F).range
  ord_zero_algebraic : ∀ (f : Fˣ), (∀ P : C, CurveWithOrd.ord P f = 0) →
    IsAlgebraic k (f : F)
  residue_eval : ∀ (P : C), ∃ (evalP : F →ₗ[k] k),
    ∀ (f : Fˣ), CurveWithOrd.ord P f ≥ 0 → evalP (f : F) = 0 →
      CurveWithOrd.ord P f ≥ 1


end CurveWithOrd
end ClosedPoint
