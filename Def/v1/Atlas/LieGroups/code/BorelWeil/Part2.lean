/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BorelWeil.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Rank
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.Algebra.Lie.Weights.RootSystem
import Structure.v1.Atlas.LieGroups.code.BorelWeil.Part2


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
