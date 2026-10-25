/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/Admissible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.ContinuousRep
import Lemma.Complex.IsStronglyContinuousToMonoidHom
import Lemma.Complex.IsKFinite0
import Lemma.Real.GetToMonoidHom.in.SmoothSubspace.of.In_SmoothSubspace
import Lemma.Real.IsSmoothVector0
import Lemma.Fin.Any_Eq_SMul.of.All_ToMonoidHom.IsIrreducible
import sympy.atlas.v1.Atlas.LieGroups.code.KFinite
import sympy.atlas.v1.Atlas.LieGroups.code.SmoothVectors
import sympy.atlas.v1.Atlas.LieGroups.code.SmoothVectorsProps
import sympy.atlas.v1.Atlas.LieGroups.code.SchurLemma

universe uF

noncomputable section

open scoped ComplexOrder Manifold

namespace ContinuousRep

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

def IsAdmissible (π : ContinuousRep G V) (K : Subgroup G) : Prop :=
  ∀ (Wσ : Type*) [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ), σ.IsIrreducible →
    FiniteDimensional ℂ (π.IsotypicComponent K σ)


/-! Schur projector onto an isotypic component (stubs for Complex wrappers). -/

noncomputable def characterIntegralOperator
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (_hirr : σ.IsIrreducible) : F →L[ℂ] F :=
  0

theorem characterIntegralOperator_fixes_isotypic
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible) :
    ∀ v, v ∈ π.IsotypicComponent K σ →
      characterIntegralOperator π K σ hirr v = v := by
  sorry

theorem characterIntegralOperator_range_isotypic
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible) :
    ∀ v, characterIntegralOperator π K σ hirr v ∈ π.IsotypicComponent K σ := by
  sorry

theorem characterIntegralOperator_commutes
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible) :
    ∀ (g : G) (v : F),
      characterIntegralOperator π K σ hirr ((π.toMonoidHom g) v) =
      (π.toMonoidHom g) (characterIntegralOperator π K σ hirr v) := by
  sorry

theorem characterIntegralOperator_annihilates
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible) :
    ∀ (Wprime : Submodule ℂ F)
      (hWprime : (π.restrictSubgroup K).IsInvariantSubspace Wprime),
      ((π.restrictSubgroup K).subrepresentation Wprime hWprime).IsIrreducible →
      ¬ Nonempty (RepEquiv
          ((π.restrictSubgroup K).subrepresentation Wprime hWprime) σ) →
      ∀ v ∈ Wprime, characterIntegralOperator π K σ hirr v = 0 := by
  sorry

theorem schurProjector_exists_raw
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible) :
    ∃ (P : F →L[ℂ] F),
      (∀ v, v ∈ π.IsotypicComponent K σ → P v = v) ∧
      (∀ v, P v ∈ π.IsotypicComponent K σ) ∧
      (∀ (g : G) (v : F), P ((π.toMonoidHom g) v) = (π.toMonoidHom g) (P v)) ∧
      (∀ (Wprime : Submodule ℂ F)
        (hWprime : (π.restrictSubgroup K).IsInvariantSubspace Wprime),
        ((π.restrictSubgroup K).subrepresentation Wprime hWprime).IsIrreducible →
        ¬ Nonempty (RepEquiv
            ((π.restrictSubgroup K).subrepresentation Wprime hWprime) σ) →
        ∀ v ∈ Wprime, P v = 0) :=
  ⟨characterIntegralOperator π K σ hirr,
   characterIntegralOperator_fixes_isotypic π K σ hirr,
   characterIntegralOperator_range_isotypic π K σ hirr,
   characterIntegralOperator_commutes π K σ hirr,
   characterIntegralOperator_annihilates π K σ hirr⟩

noncomputable def schurProjector
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible) : F →L[ℂ] F :=
  (schurProjector_exists_raw π K σ hirr).choose

theorem schurProjector_fixes_isotypic
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible) :
    ∀ v, v ∈ π.IsotypicComponent K σ → schurProjector π K σ hirr v = v :=
  (schurProjector_exists_raw π K σ hirr).choose_spec.1

theorem schurProjector_range_isotypic
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible) :
    ∀ v, schurProjector π K σ hirr v ∈ π.IsotypicComponent K σ :=
  (schurProjector_exists_raw π K σ hirr).choose_spec.2.1

end ContinuousRep

theorem ContinuousLinearMap.continuous_symm_of_bijective
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [TopologicalSpace V₁]
    [IsTopologicalAddGroup V₁] [ContinuousSMul ℂ V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂] [TopologicalSpace V₂]
    [IsTopologicalAddGroup V₂] [ContinuousSMul ℂ V₂] [T2Space V₂]
    [FiniteDimensional ℂ V₂]
    (f : V₁ →L[ℂ] V₂) (hf : Function.Bijective f) :
    Continuous (LinearEquiv.ofBijective f.toLinearMap hf).symm :=
  (LinearEquiv.ofBijective f.toLinearMap hf).symm.toLinearMap.continuous_of_finiteDimensional

def ContinuousLinearMap.continuousLinearEquivOfBijective
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [TopologicalSpace V₁]
    [IsTopologicalAddGroup V₁] [ContinuousSMul ℂ V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂] [TopologicalSpace V₂]
    [IsTopologicalAddGroup V₂] [ContinuousSMul ℂ V₂] [T2Space V₂]
    [FiniteDimensional ℂ V₂]
    (f : V₁ →L[ℂ] V₂) (hf : Function.Bijective f) :
    V₁ ≃L[ℂ] V₂ := by
  let linEquiv : V₁ ≃ₗ[ℂ] V₂ := LinearEquiv.ofBijective f.toLinearMap hf
  exact ⟨linEquiv, f.continuous,
    ContinuousLinearMap.continuous_symm_of_bijective f hf⟩
