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
import Structure.v1.Atlas.ArithmeticGeometry.code.CurveTheory.Part4


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

def DVRDominates {K₁ K₂ : Type*} [Field K₁] [Field K₂]
    (φ_star : K₂ →+* K₁)
    (R₁ : Type*) [CommRing R₁] [IsDomain R₁] [Algebra R₁ K₁] [IsFractionRing R₁ K₁]
    (R₂ : Type*) [CommRing R₂] [IsDomain R₂] [Algebra R₂ K₂] [IsFractionRing R₂ K₂] : Prop :=
  ∀ x : K₂, IsLocalization.IsInteger R₂ x → IsLocalization.IsInteger R₁ (φ_star x)

def IsConstantFieldHom {k K₁ K₂ : Type*} [Field k] [Field K₁] [Field K₂]
    [Algebra k K₁] [Algebra k K₂] (φ_star : K₂ →ₐ[k] K₁) : Prop :=
  ∀ x : K₂, φ_star x ∈ Set.range (algebraMap k K₁)

def IsSurjectiveOnPoints {k K₁ K₂ : Type*} [Field k] [Field K₁] [Field K₂]
    [Algebra k K₁] [Algebra k K₂]
    (φ_star : K₂ →ₐ[k] K₁)
    {P₁ : Type*} (R₁ : P₁ → Type*)
    [∀ p, CommRing (R₁ p)] [∀ p, IsDomain (R₁ p)] [∀ p, Algebra (R₁ p) K₁]
    [∀ p, IsFractionRing (R₁ p) K₁]
    {P₂ : Type*} (R₂ : P₂ → Type*)
    [∀ p, CommRing (R₂ p)] [∀ p, IsDomain (R₂ p)] [∀ p, Algebra (R₂ p) K₂]
    [∀ p, IsFractionRing (R₂ p) K₂] : Prop :=
  ∀ p₂ : P₂, ∃ p₁ : P₁, DVRDominates φ_star.toRingHom (R₁ p₁) (R₂ p₂)

end DVRNormalization
end ArithmeticGeometry
end
