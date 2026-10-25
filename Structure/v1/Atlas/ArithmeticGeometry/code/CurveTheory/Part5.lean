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
import Def.v1.Atlas.ArithmeticGeometry.code.CurveTheory.Part4


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

structure BiratIso
    {k K₁ K₂ : Type u} [Field k]
    [Field K₁] [Algebra k K₁] {n₁ : ℕ} (C₁ : SmoothProjectiveCurveData k K₁ n₁)
    [Field K₂] [Algebra k K₂] {n₂ : ℕ} (C₂ : SmoothProjectiveCurveData k K₂ n₂) where
  σ : K₁ ≃+* K₂
  forward : RationalMapToProj K₁ n₂
  backward : RationalMapToProj K₂ n₁
  forward_inverse : ∃ c₁ : K₁, c₁ ≠ 0 ∧
    ∀ i : Fin (n₁ + 1), σ.symm (backward.coords i) = c₁ * C₁.emb i
  backward_inverse : ∃ c₂ : K₂, c₂ ≠ 0 ∧
    ∀ i : Fin (n₂ + 1), σ (forward.coords i) = c₂ * C₂.emb i

structure CurveIso
    {k K₁ K₂ : Type u} [Field k]
    [Field K₁] [Algebra k K₁] {n₁ : ℕ} (C₁ : SmoothProjectiveCurveData k K₁ n₁)
    [Field K₂] [Algebra k K₂] {n₂ : ℕ} (C₂ : SmoothProjectiveCurveData k K₂ n₂) where
  σ : K₁ ≃+* K₂
  forward : RationalMapToProj K₁ n₂
  backward : RationalMapToProj K₂ n₁
  forward_regular : ∀ p, forward.IsRegularAt (C₁.R p)
  backward_regular : ∀ p, backward.IsRegularAt (C₂.R p)
  forward_inverse : ∃ c₁ : K₁, c₁ ≠ 0 ∧
    ∀ i : Fin (n₁ + 1), σ.symm (backward.coords i) = c₁ * C₁.emb i
  backward_inverse : ∃ c₂ : K₂, c₂ ≠ 0 ∧
    ∀ i : Fin (n₂ + 1), σ (forward.coords i) = c₂ * C₂.emb i

end DVRNormalization
end ArithmeticGeometry
end
