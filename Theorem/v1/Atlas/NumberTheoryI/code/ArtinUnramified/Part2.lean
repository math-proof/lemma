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
import Abbrev.v1.Atlas.NumberTheoryI.code.ArtinUnramified


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
