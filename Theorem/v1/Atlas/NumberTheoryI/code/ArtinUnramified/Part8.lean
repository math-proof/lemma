module
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Theorem.Set.Closure.eq.N.of.Eq
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.RingTheory.FractionalIdeal.Extended
public import Mathlib.RingTheory.Invariant.Basic
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Lemma247
public import Def.v1.Atlas.NumberTheoryI.code.ArtinUnramified.Part11


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open scoped Pointwise

open NumberField

namespace ArtinUnramified

attribute [instance] CyclicExtensionData.instGroupG
  CyclicExtensionData.instFiniteG CyclicExtensionData.instCyclicG
  CyclicExtensionData.instCommGroupM CyclicExtensionData.instFiniteM
  CyclicExtensionData.instAction

lemma subgroup_fg_of_comm_fg {L : Type*} [Field L] [NumberField L] (H : Subgroup (𝓞 L)ˣ) : H.FG := by
  rw [Subgroup.fg_iff_add_fg]
  haveI : Monoid.FG (𝓞 L)ˣ := inferInstance
  haveI : Module.Finite ℤ (Additive (𝓞 L)ˣ) := AddMonoid.FG.to_moduleFinite_int
  haveI : IsNoetherian ℤ (Additive (𝓞 L)ˣ) := isNoetherian_of_isNoetherianRing_of_finite ℤ _
  have hfg_mod : (H.toAddSubgroup.toIntSubmodule : Submodule ℤ (Additive (𝓞 L)ˣ)).FG :=
    IsNoetherian.noetherian _
  rwa [Submodule.fg_iff_addSubgroup_fg, AddSubgroup.toIntSubmodule_toAddSubgroup] at hfg_mod

lemma pow_card_mem_augmentationUnitsSubgroup (K L : Type*)
    [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    [Fintype (L ≃ₐ[K] L)]
    (u : (𝓞 L)ˣ) (hu : normMapUnits K L u = 1) :
    u ^ Fintype.card (L ≃ₐ[K] L) ∈ augmentationUnitsSubgroup K L := by
  have key : u ^ Fintype.card (L ≃ₐ[K] L) = ∏ σ : (L ≃ₐ[K] L), (u * (σ • u)⁻¹) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Finset.prod_inv_distrib]
    simp only [normMapUnits, MonoidHom.coe_mk, OneHom.coe_mk] at hu
    rw [hu, inv_one, mul_one]
  rw [key]
  apply Subgroup.prod_mem
  intro σ _
  have : u * (σ • u)⁻¹ = (σ • u * u⁻¹)⁻¹ := by group
  rw [this]
  apply Subgroup.inv_mem
  apply Subgroup.subset_closure
  exact ⟨σ, u, rfl⟩

end ArtinUnramified
end
