/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/Globalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.GKModule.Part2
import Def.v1.Atlas.LieGroups.code.GKModuleDefs.Part2
import Def.v1.Atlas.LieGroups.code.DixmierLemma
import Lemma.Set.In_RangeAlgebraMap.of.IsAlgebraic
import Theorem.v1.Atlas.LieGroups.code.InfinitesimalEquivalence
import Mathlib.LinearAlgebra.FreeAlgebra
import Mathlib.Topology.DenseEmbedding
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.OfAssociative


noncomputable section

open scoped Cardinal

def gkmoduleSubScalar
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (φ : GKModuleHom M M) (c : ℂ) : GKModuleHom M M where
  toLinearMap := φ.toLinearMap - c • LinearMap.id
  lie_comm := by
    intro X v
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [φ.lie_comm, lie_sub, lie_smul]
  group_comm := by
    intro k v
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [φ.group_comm, map_sub, map_smul]

noncomputable def ueaAction (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V] :
    UniversalEnvelopingAlgebra ℂ 𝔤 →ₐ[ℂ] Module.End ℂ V :=
  UniversalEnvelopingAlgebra.lift ℂ (LieModule.toEnd ℂ 𝔤 V)

def IsGIntertwiner
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Type*} [Group K] {K_sub : K →* G}
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [LieRingModule 𝔤 V₁] [LieModule ℂ 𝔤 V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    [LieRingModule 𝔤 V₂] [LieModule ℂ 𝔤 V₂]
    {M₁ : GKModule 𝔤 K 𝔨 Ad V₁} {M₂ : GKModule 𝔤 K 𝔨 Ad V₂}
    (G₁ : Globalization G K_sub M₁) (G₂ : Globalization G K_sub M₂)
    (T : G₁.Ŵ → G₂.Ŵ) : Prop :=
  ∀ (g : G) (w : G₁.Ŵ), T (G₁.πApp g w) = G₂.πApp g (T w)

def IsGlobAdditive
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Type*} [Group K] {K_sub : K →* G}
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [LieRingModule 𝔤 V₁] [LieModule ℂ 𝔤 V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    [LieRingModule 𝔤 V₂] [LieModule ℂ 𝔤 V₂]
    {M₁ : GKModule 𝔤 K 𝔨 Ad V₁} {M₂ : GKModule 𝔤 K 𝔨 Ad V₂}
    (G₁ : Globalization G K_sub M₁) (G₂ : Globalization G K_sub M₂)
    (T : G₁.Ŵ → G₂.Ŵ) : Prop :=
  ∀ (x y : G₁.Ŵ),
    T (@HAdd.hAdd G₁.Ŵ G₁.Ŵ G₁.Ŵ
        (@instHAdd G₁.Ŵ G₁.addCommGroupŴ.toAddGroup.toAddMonoid.toAdd) x y) =
      @HAdd.hAdd G₂.Ŵ G₂.Ŵ G₂.Ŵ
        (@instHAdd G₂.Ŵ G₂.addCommGroupŴ.toAddGroup.toAddMonoid.toAdd) (T x) (T y)

def IsGlobLinear
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Type*} [Group K] {K_sub : K →* G}
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [LieRingModule 𝔤 V₁] [LieModule ℂ 𝔤 V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    [LieRingModule 𝔤 V₂] [LieModule ℂ 𝔤 V₂]
    {M₁ : GKModule 𝔤 K 𝔨 Ad V₁} {M₂ : GKModule 𝔤 K 𝔨 Ad V₂}
    (G₁ : Globalization G K_sub M₁) (G₂ : Globalization G K_sub M₂)
    (T : G₁.Ŵ → G₂.Ŵ) : Prop :=
  ∀ (c : ℂ) (x : G₁.Ŵ),
    T (@HSMul.hSMul ℂ G₁.Ŵ G₁.Ŵ (@instHSMul ℂ G₁.Ŵ G₁.moduleŴ.toSMul) c x) =
      @HSMul.hSMul ℂ G₂.Ŵ G₂.Ŵ (@instHSMul ℂ G₂.Ŵ G₂.moduleŴ.toSMul) c (T x)

end
