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
public import Structure.v1.Atlas.LieGroups.code.BorelWeil.Part3

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

def SkewSymmetricBilinearForm.IsNondegenerate {k : Type*} {M : Type*} [CommRing k]
    [AddCommGroup M] [Module k M] (ω : SkewSymmetricBilinearForm k M) : Prop :=
  ∀ x : M, (∀ y : M, ω.bilin x y = 0) → x = 0

def kirillovKostantForm (k : Type*) (𝔤 : Type*) [CommRing k]
    [LieRing 𝔤] [LieAlgebra k 𝔤]
    (f : 𝔤 →ₗ[k] k) : SkewSymmetricBilinearForm k 𝔤 where
  bilin := {
    toFun := fun y => {
      toFun := fun z => f ⁅y, z⁆
      map_add' := by intro z₁ z₂; rw [lie_add, map_add]
      map_smul' := by
        intro r z; rw [lie_smul, map_smul]; simp [RingHom.id_apply, smul_eq_mul]
    }
    map_add' := by
      intro y₁ y₂; ext z
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
      rw [add_lie, map_add]
    map_smul' := by
      intro r y; ext z
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      rw [smul_lie, map_smul, smul_eq_mul]
  }
  skew_symm := by
    intro x y
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [← lie_skew, map_neg]

def coadjointStabilizer (k : Type*) (𝔤 : Type*) [CommRing k]
    [LieRing 𝔤] [LieAlgebra k 𝔤]
    (f : 𝔤 →ₗ[k] k) : Submodule k 𝔤 where
  carrier := {x : 𝔤 | ∀ y : 𝔤, f ⁅x, y⁆ = 0}
  add_mem' := by
    intro a b ha hb y
    rw [add_lie, map_add, ha y, hb y, add_zero]
  zero_mem' := by
    intro y; rw [zero_lie, map_zero]
  smul_mem' := by
    intro r a ha y
    rw [smul_lie, map_smul, ha y, smul_zero]

end
