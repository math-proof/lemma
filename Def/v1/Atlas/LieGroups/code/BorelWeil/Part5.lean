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
public import Instance.v1.Atlas.LieGroups.code.BorelWeil

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

def SatisfiesSerreR1 (R : Type*) [CommRing R] : Prop :=
  ∀ (𝔭 : Ideal R) [𝔭.IsPrime], 𝔭.height ≤ 1 →
    IsRegularLocalRing (Localization.AtPrime 𝔭)

def SatisfiesSerreS2 (R : Type*) [CommRing R] : Prop :=
  ∀ (𝔭 : Ideal R) [𝔭.IsPrime], 𝔭.height ≥ 2 →
    ∃ (a b : Localization.AtPrime 𝔭),
      a ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) ∧
      (∀ x : Localization.AtPrime 𝔭, x * a = 0 → x = 0) ∧
      b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) ∧
      (∀ x : Localization.AtPrime 𝔭, x * b ∈ Ideal.span {a} → x ∈ Ideal.span {a})

def IsGradedAlgEquiv {k : Type*} [CommSemiring k]
    {A : Type*} [Semiring A] [Algebra k A]
    {B : Type*} [Semiring B] [Algebra k B]
    (𝒜 : ℕ → Submodule k A) (ℬ : ℕ → Submodule k B)
    (e : A ≃ₐ[k] B) : Prop :=
  ∀ n : ℕ, ∀ a : A, a ∈ 𝒜 n ↔ e a ∈ ℬ n

end
