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
import Structure.v1.Atlas.ArithmeticGeometry.code.CurveTheory.Part5


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

def SmoothProjectiveCurve.birational_map_is_isomorphism
    {k K₁ K₂ : Type u} [Field k]
    [Field K₁] [Algebra k K₁] {n₁ : ℕ} {C₁ : SmoothProjectiveCurveData k K₁ n₁}
    [Field K₂] [Algebra k K₂] {n₂ : ℕ} {C₂ : SmoothProjectiveCurveData k K₂ n₂}
    (Φ : BiratIso C₁ C₂) : CurveIso C₁ C₂ :=
  { σ := Φ.σ
    forward := Φ.forward
    backward := Φ.backward
    forward_regular :=
      @SmoothProjectiveCurve.rational_map_is_morphism K₁ _ C₁.P _ Φ.forward C₁.R _ _ _ _ _
    backward_regular :=
      @SmoothProjectiveCurve.rational_map_is_morphism K₂ _ C₂.P _ Φ.backward C₂.R _ _ _ _ _
    forward_inverse := Φ.forward_inverse
    backward_inverse := Φ.backward_inverse }

namespace FunctionField_k

variable {k : Type*} [Field k]

variable {F₁ : Type*} {F₂ : Type*} [Field F₁] [Field F₂]

def localizationSubalgebraCarrier (S : Subalgebra k F) [IsFractionRing S F]
    (𝔭 : Ideal S) [𝔭.IsPrime] : Set F :=
  {x : F | ∃ (a : S) (b : 𝔭.primeCompl),
    x * algebraMap S F b.1 = algebraMap S F a}

section Lemma18_11_Helpers

def dvrSubalgebraToValuationSubring
    (R : Subalgebra k F) [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] :
    ValuationSubring F where
  toSubring := R.toSubring
  mem_or_inv_mem' := by
    intro x
    haveI : ValuationRing R := of_isDiscreteValuationRing R
    rcases ValuationRing.isInteger_or_isInteger R x with ⟨a, ha⟩ | ⟨a, ha⟩
    · left; show x ∈ (R : Set F); rw [← ha]; exact a.2
    · right; show x⁻¹ ∈ (R : Set F); rw [← ha]; exact a.2


end Lemma18_11_Helpers
end FunctionField_k
end DVRNormalization
end ArithmeticGeometry
end
