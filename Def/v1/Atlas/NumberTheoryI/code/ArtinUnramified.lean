/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.Algebra.Set.Closure.eq.N.of.Eq
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.Invariant.Basic
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Lemma247


noncomputable section

open scoped Pointwise

open NumberField

namespace ArtinUnramified

omit [FiniteDimensional K L] [IsGalois K L] in
def sigmaMinusOneMap (σ : L ≃ₐ[K] L) : L →ₗ[K] L :=
  σ.toLinearMap - LinearMap.id

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
