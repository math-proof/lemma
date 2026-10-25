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
import Instance.v1.Atlas.ArithmeticGeometry.code.CurveTheory.Part4


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

def BiratIso.ofSameFunctionField
    {k F : Type u} [Field k] [Field F] [Algebra k F]
    {n₁ : ℕ} (C₁ : SmoothProjectiveCurveData k F n₁)
    {n₂ : ℕ} (C₂ : SmoothProjectiveCurveData k F n₂) :
    BiratIso C₁ C₂ where
  σ := RingEquiv.refl F
  forward := ⟨C₂.emb, C₂.emb_ne_zero⟩
  backward := ⟨C₁.emb, C₁.emb_ne_zero⟩
  forward_inverse := ⟨1, one_ne_zero, fun i => by simp [RingEquiv.refl_apply]⟩
  backward_inverse := ⟨1, one_ne_zero, fun i => by simp [RingEquiv.refl_apply]⟩

def unique_smooth_model_uniqueness
    {k F : Type u} [Field k] [Field F] [Algebra k F]
    {n₁ : ℕ} (C₁ : SmoothProjectiveCurveData k F n₁)
    {n₂ : ℕ} (C₂ : SmoothProjectiveCurveData k F n₂) :
    CurveIso C₁ C₂ :=
  SmoothProjectiveCurve.birational_map_is_isomorphism (BiratIso.ofSameFunctionField C₁ C₂)

end Lemma18_11_Helpers
end FunctionField_k
end DVRNormalization
end ArithmeticGeometry
end
