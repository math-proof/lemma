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
import Structure.v1.Atlas.ArithmeticGeometry.code.CurveTheory.Part8


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

noncomputable def SmoothProjectiveCurveData.pointValSubring
    {k K : Type u} [Field k] [Field K] [Algebra k K] {n : ℕ} (C : SmoothProjectiveCurveData k K n) (p : C.P) :
    ValuationSubring K where
  toSubring := (algebraMap (C.R p) K).range
  mem_or_inv_mem' x := by
    haveI : ValuationRing (C.R p) := of_isDiscreteValuationRing (C.R p)
    rcases ValuationRing.isInteger_or_isInteger (C.R p) x with ⟨r, hr⟩ | ⟨r, hr⟩
    · left; exact ⟨r, hr⟩
    · right; exact ⟨r, hr⟩

end Lemma18_11_Helpers
end FunctionField_k
end DVRNormalization
end ArithmeticGeometry
end
