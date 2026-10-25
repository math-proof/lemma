/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/InfinitesimalEquivalenceCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.GKModule.Part2
import Def.v1.Atlas.LieGroups.code.GKModuleDefs.Part2
import Structure.v1.Atlas.LieGroups.code.HarishChandraFunctor
import Lemma.Bijective.EqContinuousLinearEquivOfBijective.of.Bijective
import Def.v1.Atlas.LieGroups.code.Admissible.Part3
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Structure.v1.Atlas.LieGroups.code.InfinitesimalEquivalenceCore


noncomputable section

def InfinitesimallyEquivalent
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [LieRingModule 𝔤 V₁] [LieModule ℂ 𝔤 V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    [LieRingModule 𝔤 V₂] [LieModule ℂ 𝔤 V₂]
    (M₁ : GKModule 𝔤 K 𝔨 Ad V₁) (M₂ : GKModule 𝔤 K 𝔨 Ad V₂) : Prop :=
  Nonempty (GKModuleIso M₁ M₂)

end
