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
public import Instance.v1.Atlas.NumberTheoryI.code.ArtinUnramified.Part2


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

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

def normMapUnits [Fintype (L ≃ₐ[K] L)] : (𝓞 L)ˣ →* (𝓞 L)ˣ where
  toFun u := ∏ σ : (L ≃ₐ[K] L), σ • u
  map_one' := by simp
  map_mul' u v := by
    show ∏ σ : (L ≃ₐ[K] L), σ • (u * v) =
      (∏ σ : (L ≃ₐ[K] L), σ • u) * (∏ σ : (L ≃ₐ[K] L), σ • v)
    simp_rw [smul_mul']; exact Finset.prod_mul_distrib

def unitsFixed : Subgroup (𝓞 L)ˣ :=
  FixedPoints.subgroup (L ≃ₐ[K] L) (𝓞 L)ˣ

def normImageUnitsSubgroup [Fintype (L ≃ₐ[K] L)] : Subgroup (𝓞 L)ˣ :=
  (normMapUnits K L).range

def normKerUnits [Fintype (L ≃ₐ[K] L)] : Subgroup (𝓞 L)ˣ :=
  (normMapUnits K L).ker

def augmentationUnitsSubgroup : Subgroup (𝓞 L)ˣ :=
  Subgroup.closure {x : (𝓞 L)ˣ | ∃ (σ : L ≃ₐ[K] L) (u : (𝓞 L)ˣ), x = σ • u * u⁻¹}

end ArtinUnramified
end
