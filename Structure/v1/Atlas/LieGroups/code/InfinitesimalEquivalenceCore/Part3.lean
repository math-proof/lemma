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
import Def.v1.Atlas.LieGroups.code.InfinitesimalEquivalenceCore.Part2


noncomputable section

structure Globalization
    (G : Type*) [Group G] [TopologicalSpace G]
    {K : Type*} [Group K]
    (K_sub : K →* G)
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) where
  Ŵ : Type*
  instNACG : NormedAddCommGroup Ŵ
  instIPS : @InnerProductSpace ℂ Ŵ _ instNACG.toSeminormedAddCommGroup
  instCS : @CompleteSpace Ŵ instNACG.toUniformSpace
  π : @ContinuousRep G _ _ Ŵ instNACG.toAddCommGroup instIPS.toNormedSpace.toModule
      instNACG.toUniformSpace.toTopologicalSpace
  isUnitary : @ContinuousRep.IsUnitary G _ _ Ŵ instNACG instIPS instCS π
  isIrreducible : @ContinuousRep.IsIrreducible G _ _ Ŵ
      instNACG.toAddCommGroup instIPS.toNormedSpace.toModule
      instNACG.toUniformSpace.toTopologicalSpace π
  ι : @LinearMap ℂ ℂ _ _ (RingHom.id ℂ) V Ŵ
      _ instNACG.toAddCommGroup.toAddCommMonoid _ instIPS.toNormedSpace.toModule
  ι_injective : Function.Injective ι
  K_compat : ∀ (k : K) (v : V), ι (M.σ k v) = (π.toMonoidHom (K_sub k)) (ι v)
  lie_action_Ŵ : 𝔤 → Ŵ → Ŵ
  lie_compat_ι : ∀ (X : 𝔤) (v : V), ι ⁅X, v⁆ = lie_action_Ŵ X (ι v)
  kfin_image : Set.range ι =
    ↑(@ContinuousRep.kFiniteSubspace G _ _ Ŵ
      instNACG.toAddCommGroup instIPS.toNormedSpace.toModule
      instNACG.toUniformSpace.toTopologicalSpace
      π K_sub.range)

end
