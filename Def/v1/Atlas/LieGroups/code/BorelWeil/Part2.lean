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
public import Structure.v1.Atlas.LieGroups.code.BorelWeil.Part2

@[expose] public section

noncomputable section

universe u v

attribute [instance] BorelWeilData.field_k BorelWeilData.lieRing BorelWeilData.lieAlgebra
  BorelWeilData.group_G BorelWeilData.wl_addCommGroup BorelWeilData.irrepAddCommGroup
  BorelWeilData.irrepModule BorelWeilData.irrepFinDim BorelWeilData.sectionsAddCommGroup
  BorelWeilData.sectionsModule

attribute [instance] ParabolicBorelWeilData.pfSectionsAddCommGroup
  ParabolicBorelWeilData.pfSectionsModule

attribute [instance] SpringerResolutionData.field_k SpringerResolutionData.lieRing
  SpringerResolutionData.lieAlgebra

def SpringerResolutionData.closedEmbedding (D : SpringerResolutionData) :
    D.CotangentBundle → D.FlagVar × D.𝔤 :=
  fun y => (D.bundleProjection y, D.springerMap y)

noncomputable def SpringerResolutionData.mk' (k : Type*) [Field k] (𝔤 : Type*)
    [LieRing 𝔤] [LieAlgebra k 𝔤]
    (FlagVar CotangentBundle : Type*)
    (springerMap : CotangentBundle → 𝔤)
    (bundleProjection : CotangentBundle → FlagVar)
    (IsRegularNilpotent : 𝔤 → Prop)
    (hSpringerMap_mem : ∀ y : CotangentBundle, springerMap y ∈ nilpotentCone k 𝔤)
    (hCotangentBundle_ext : ∀ y₁ y₂ : CotangentBundle,
      bundleProjection y₁ = bundleProjection y₂ →
      springerMap y₁ = springerMap y₂ → y₁ = y₂)
    (hRegNilpMem : ∀ e, IsRegularNilpotent e → e ∈ nilpotentCone k 𝔤)
    (hRegNilpNonempty : ∃ e, IsRegularNilpotent e)
    (isInBorel : 𝔤 → FlagVar → Prop)
    (hIsInBorel_of_springerMap : ∀ y : CotangentBundle,
      isInBorel (springerMap y) (bundleProjection y))
    (rho_dual : 𝔤) :
    SpringerResolutionData where
  k := k
  𝔤 := 𝔤
  FlagVar := FlagVar
  CotangentBundle := CotangentBundle
  springerMap := springerMap
  springerMap_mem_nilpotentCone := hSpringerMap_mem
  bundleProjection := bundleProjection
  cotangentBundle_ext := hCotangentBundle_ext
  IsRegularNilpotent := IsRegularNilpotent
  regularNilpotent_mem := hRegNilpMem
  regularNilpotent_nonempty := hRegNilpNonempty
  isInBorel := isInBorel
  isInBorel_of_springerMap := hIsInBorel_of_springerMap
  rho_dual := rho_dual

end
