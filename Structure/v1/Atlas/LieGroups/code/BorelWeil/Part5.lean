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
public import Def.v1.Atlas.LieGroups.code.BorelWeil.Part4


public noncomputable section

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

structure NilpotentConeOrbitData (k : Type*) (𝔤 : Type*)
    [Field k] [LieRing 𝔤] [LieAlgebra k 𝔤]
    [Module.Finite k 𝔤] [Module.Free k 𝔤] [LieAlgebra.IsSemisimple k 𝔤] where
  dimVariety : Set 𝔤 → ℕ
  dim_nilpCone_eq : dimVariety (nilpotentCone k 𝔤) = Module.finrank k 𝔤 - LieAlgebra.rank k 𝔤
  dim_nilpCone_even : Even (dimVariety (nilpotentCone k 𝔤))
  dim_singLocus_even : Even (dimVariety (nilpotentCone_singularLocus k 𝔤))
  dim_singLocus_lt : dimVariety (nilpotentCone_singularLocus k 𝔤) < dimVariety (nilpotentCone k 𝔤)

structure NilpotentConeCoordRingData (k : Type*) (𝔤 : Type*)
    [Field k] [LieRing 𝔤] [LieAlgebra k 𝔤] where
  SymAlg : Type*
  [symAlgCommRing : CommRing SymAlg]
  [symAlgAlgebra : Algebra k SymAlg]
  eval_𝔤 : SymAlg →ₐ[k] (𝔤 → k)
  vanishingIdeal : Ideal SymAlg
  mem_vanishingIdeal : ∀ f : SymAlg,
    f ∈ vanishingIdeal ↔ ∀ x ∈ nilpotentCone k 𝔤, eval_𝔤 f x = 0
  [symAlg_isNoetherian : IsNoetherianRing SymAlg]
  [vanishingIdeal_isPrime : vanishingIdeal.IsPrime]

end
