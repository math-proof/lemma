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
public import Theorem.v1.Atlas.LieGroups.code.BorelWeil

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

attribute [instance] CoadjointOrbitData.instGroup

variable {k' : Type*} {𝔤' : Type*} [CommRing k'] [LieRing 𝔤'] [LieAlgebra k' 𝔤']

attribute [instance] NilpotentConeCoordRingData.symAlgCommRing
  NilpotentConeCoordRingData.symAlgAlgebra
  NilpotentConeCoordRingData.symAlg_isNoetherian
  NilpotentConeCoordRingData.vanishingIdeal_isPrime

instance NilpotentConeCoordRingData.instIsDomainCoordRing
    {k : Type*} {𝔤 : Type*} [Field k] [LieRing 𝔤] [LieAlgebra k 𝔤]
    [LieAlgebra.IsSemisimple k 𝔤] [Module.Finite k 𝔤]
    (D : NilpotentConeCoordRingData k 𝔤) : IsDomain D.coordRing :=
  nilpotentCone_coordRing_isDomain D

instance NilpotentConeCoordRingData.instIsNoetherianCoordRing
    {k : Type*} {𝔤 : Type*} [Field k] [LieRing 𝔤] [LieAlgebra k 𝔤]
    (D : NilpotentConeCoordRingData k 𝔤) : IsNoetherianRing D.coordRing :=
  Ideal.Quotient.isNoetherianRing D.vanishingIdeal

end
