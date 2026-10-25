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
import Def.v1.Atlas.ArithmeticGeometry.code.Divisors.Part10
attribute [instance] ClosedPointRes.residueFieldField ClosedPointRes.residueFieldAlgebra
    ClosedPointRes.finiteDimensional


namespace ClosedPoint

variable {G : Type*} {C : Type*} [Group G] [MulAction G C]

namespace CurveWithOrd

variable {C : Type*} {F : Type*} [Field F] [FunctionFieldCurve C F]

noncomputable section

namespace CurveWithConstants

variable {C : Type*} {k : Type*} {F : Type*} [Field k] [Field F]
  [Algebra k F] [CurveWithConstants C k F]

open CurveWithOrd CurveDivisor

structure CurveMorphismData (C₁ : Type*) (C₂ : Type*) where
  toFun : C₁ → C₂
  ramificationIndex : C₁ → ℤ
  fiber : C₂ → Finset C₁
  fiber_maps_to : ∀ Q : C₂, ∀ P ∈ fiber Q, toFun P = Q
  fiber_complete : ∀ Q : C₂, ∀ P : C₁, toFun P = Q → P ∈ fiber Q
  residueFieldDegreeRatio : C₁ → ℤ

end CurveWithConstants
end
end CurveWithOrd
end ClosedPoint
