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
import Def.v1.Atlas.LieGroups.code.BorelWeil


noncomputable section

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
