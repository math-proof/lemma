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
import Theorem.v1.Atlas.LieGroups.code.Admissible.Part2
universe uF


noncomputable section

open scoped ComplexOrder Manifold

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

end
