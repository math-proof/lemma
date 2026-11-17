/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.RingTheory.FractionalIdeal.Extended
public import Mathlib.RingTheory.Invariant.Basic

@[expose] public section

noncomputable section

open scoped Pointwise

open NumberField

namespace ArtinUnramified

section CyclicCohomology

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

omit [FiniteDimensional K L] [IsGalois K L] in
def sigmaMinusOneMap (σ : L ≃ₐ[K] L) : L →ₗ[K] L :=
  σ.toLinearMap - LinearMap.id

end CyclicCohomology

def DecompositionGroupOfPlace {G : Type*} [Group G] {W : Type*}
    [MulAction G W] (w : W) : Subgroup G :=
  MulAction.stabilizer G w

section RamificationDefs

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def e₀ : ℕ :=
  ∏ᶠ (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
    𝔭.asIdeal.ramificationIdxIn (𝓞 L)

def nRamifiedInfinitePlaces : ℕ := by
  classical
  exact Finset.card (Finset.filter
    (fun (w : InfinitePlace K) => ¬ InfinitePlace.IsUnramifiedIn L w) Finset.univ)

def e_inf : ℕ :=
  2 ^ nRamifiedInfinitePlaces K L

def e : ℕ := e₀ K L * e_inf K L

end RamificationDefs
end ArtinUnramified
end
