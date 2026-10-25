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
import Structure.v1.Atlas.ArithmeticGeometry.code.Divisors.Part3
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

noncomputable section

namespace CurveMorphismData

variable {C₁ C₂ : Type*}


def pullbackPoint (φ : CurveMorphismData C₁ C₂) (Q : C₂) : CurveDivisor C₁ :=
  (φ.fiber Q).sum (fun P => Finsupp.single P (φ.ramificationIndex P))

def pullback (φ : CurveMorphismData C₁ C₂) : CurveDivisor C₂ →+ CurveDivisor C₁ :=
  Finsupp.liftAddHom (fun Q => {
    toFun := fun n => n • φ.pullbackPoint Q
    map_zero' := by simp
    map_add' := by intros; simp [add_smul]
  })


def pushforward (φ : CurveMorphismData C₁ C₂) : CurveDivisor C₁ →+ CurveDivisor C₂ :=
  Finsupp.liftAddHom (fun P => {
    toFun := fun n => Finsupp.single (φ.toFun P) n
    map_zero' := by simp
    map_add' := by intros; simp [Finsupp.single_add]
  })

def pushforwardGeneral (φ : CurveMorphismData C₁ C₂) : CurveDivisor C₁ →+ CurveDivisor C₂ :=
  Finsupp.liftAddHom (fun P => {
    toFun := fun n => Finsupp.single (φ.toFun P) (n * φ.residueFieldDegreeRatio P)
    map_zero' := by simp
    map_add' := by intros; simp [Finsupp.single_add, add_mul]
  })


end CurveMorphismData
end
end CurveWithConstants
end
end CurveWithOrd
end ClosedPoint
