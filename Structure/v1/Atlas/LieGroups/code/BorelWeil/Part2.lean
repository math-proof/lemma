/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BorelWeil.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.Nilpotent
public import Mathlib.Algebra.Lie.Rank
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.Algebra.Lie.Weights.Killing
public import Mathlib.Algebra.Lie.Weights.RootSystem
public import Def.v1.Atlas.LieGroups.code.BorelWeil


public noncomputable section

universe u v

attribute [instance] BorelWeilData.field_k BorelWeilData.lieRing BorelWeilData.lieAlgebra
  BorelWeilData.group_G BorelWeilData.wl_addCommGroup BorelWeilData.irrepAddCommGroup
  BorelWeilData.irrepModule BorelWeilData.irrepFinDim BorelWeilData.sectionsAddCommGroup
  BorelWeilData.sectionsModule

attribute [instance] ParabolicBorelWeilData.pfSectionsAddCommGroup
  ParabolicBorelWeilData.pfSectionsModule

structure SpringerResolutionData where
  (k : Type u)
  [field_k : Field k]
  (𝔤 : Type v)
  [lieRing : LieRing 𝔤]
  [lieAlgebra : LieAlgebra k 𝔤]
  (FlagVar : Type*)
  (CotangentBundle : Type*)
  (springerMap : CotangentBundle → 𝔤)
  (springerMap_mem_nilpotentCone :
    ∀ y : CotangentBundle, springerMap y ∈ nilpotentCone k 𝔤)
  (bundleProjection : CotangentBundle → FlagVar)
  (cotangentBundle_ext : ∀ y₁ y₂ : CotangentBundle,
    bundleProjection y₁ = bundleProjection y₂ →
    springerMap y₁ = springerMap y₂ → y₁ = y₂)
  (IsRegularNilpotent : 𝔤 → Prop)
  (regularNilpotent_mem : ∀ e, IsRegularNilpotent e → e ∈ nilpotentCone k 𝔤)
  (regularNilpotent_nonempty : ∃ e, IsRegularNilpotent e)
  (isInBorel : 𝔤 → FlagVar → Prop)
  (isInBorel_of_springerMap : ∀ y : CotangentBundle,
    isInBorel (springerMap y) (bundleProjection y))
  (rho_dual : 𝔤)

end
