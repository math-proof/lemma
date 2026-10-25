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
import Structure.v1.Atlas.LieGroups.code.BorelWeil.Part4


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

attribute [instance] CoadjointOrbitData.instGroup

variable {k' : Type*} {𝔤' : Type*} [CommRing k'] [LieRing 𝔤'] [LieAlgebra k' 𝔤']

def CoadjointOrbitData.orbit (data : CoadjointOrbitData k' 𝔤') (f : 𝔤' →ₗ[k'] k') :
    Set (𝔤' →ₗ[k'] k') :=
  Set.range (fun g => data.coadjointAction g f)

def nilpotentCone_singularLocus (k : Type*) (𝔤 : Type*)
    [CommRing k] [LieRing 𝔤] [LieAlgebra k 𝔤] [Module.Finite k 𝔤] [Module.Free k 𝔤] :
    Set 𝔤 :=
  {x ∈ nilpotentCone k 𝔤 |
    Module.finrank k (LinearMap.ker (LieAlgebra.ad k 𝔤 x : 𝔤 →ₗ[k] 𝔤)) ≠
      LieAlgebra.rank k 𝔤}

end
