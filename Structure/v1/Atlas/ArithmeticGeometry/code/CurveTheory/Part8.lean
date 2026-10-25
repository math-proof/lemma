/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CurveTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ArithmeticGeometry.code.MorphismsCurves
import Abbrev.v1.Atlas.ArithmeticGeometry.code.RegularLocalRings
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RegularLocalRings
import Def.v1.Atlas.ArithmeticGeometry.code.CurveTheory.Part7


noncomputable section

open Module IsDiscreteValuationRing

namespace ArithmeticGeometry

section DVRNormalization

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

attribute [instance] SmoothProjectiveCurveData.instCR SmoothProjectiveCurveData.instID
  SmoothProjectiveCurveData.instDVR SmoothProjectiveCurveData.instAlg
  SmoothProjectiveCurveData.instFR SmoothProjectiveCurveData.instAlgKR
  SmoothProjectiveCurveData.instScalarTower

namespace FunctionField_k

variable {k : Type*} [Field k]

variable {F₁ : Type*} {F₂ : Type*} [Field F₁] [Field F₂]

section Lemma18_11_Helpers

attribute [instance] DVROfFunctionField.isDVR DVROfFunctionField.isFractionRing

structure AbstractCurveMorphism (k F₁ F₂ : Type*) [Field k] [Field F₁] [Field F₂]
    [Algebra k F₁] [Algebra k F₂] where
  toFun : DVROfFunctionField k F₁ → DVROfFunctionField k F₂
  pullback : F₂ →+* F₁
  pullback_comp : ∀ (a : k), pullback (algebraMap k F₂ a) = algebraMap k F₁ a
  pullback_regular : ∀ (P : DVROfFunctionField k F₁) (f : F₂),
    f ∈ (toFun P).valRing → pullback f ∈ P.valRing

end Lemma18_11_Helpers
end FunctionField_k
end DVRNormalization
end ArithmeticGeometry
end
