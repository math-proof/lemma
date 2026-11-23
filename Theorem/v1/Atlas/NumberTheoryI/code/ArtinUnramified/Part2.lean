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
public import Theorem.Set.Closure.eq.N.of.Eq
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.RingTheory.FractionalIdeal.Extended
public import Mathlib.RingTheory.Invariant.Basic
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Lemma247
public import Abbrev.v1.Atlas.NumberTheoryI.code.ArtinUnramified

public section

noncomputable section

open scoped Pointwise

open NumberField

namespace ArtinUnramified

section GaloisClassGroupAction

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

set_option maxHeartbeats 800000 in
omit [NumberField L] [FiniteDimensional K L] in
lemma galRingEquiv_mul (σ τ : L ≃ₐ[K] L) :
    galRingEquiv K L (σ * τ) = (galRingEquiv K L τ).trans (galRingEquiv K L σ) := by
  simp only [galRingEquiv]; rw [map_mul (galRestrict (𝓞 K) K L (𝓞 L))]; rfl

set_option maxHeartbeats 800000 in
omit [NumberField L] [FiniteDimensional K L] in
lemma galRingEquiv_one :
    galRingEquiv K L 1 = RingEquiv.refl (𝓞 L) := by
  simp only [galRingEquiv]; rw [map_one (galRestrict (𝓞 K) K L (𝓞 L))]; rfl

end GaloisClassGroupAction
end ArtinUnramified
end
