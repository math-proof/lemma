/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/Admissible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part3
import Lemma.Complex.IsStronglyContinuousToMonoidHom
import Lemma.Complex.IsKFinite0
import Lemma.Real.GetToMonoidHom.in.SmoothSubspace.of.In_SmoothSubspace
import Lemma.Real.IsSmoothVector0
import Lemma.Fin.Any_Eq_SMul.of.All_ToMonoidHom.IsIrreducible
import Def.v1.Atlas.LieGroups.code.KFinite.Part3
import Def.v1.Atlas.LieGroups.code.SmoothVectors
import Theorem.v1.Atlas.LieGroups.code.SmoothVectorsProps
import Def.v1.Atlas.LieGroups.code.SchurLemma
import Def.v1.Atlas.LieGroups.code.Admissible.Part2
universe uF


noncomputable section

open scoped ComplexOrder Manifold

namespace ContinuousRep

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

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

end
