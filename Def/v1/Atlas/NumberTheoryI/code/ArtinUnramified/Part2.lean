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
import Theorem.v1.Atlas.NumberTheoryI.code.ArtinUnramified.Part2


noncomputable section

open scoped Pointwise

open NumberField

namespace ArtinUnramified

section GaloisClassGroupAction

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

def mapIdealGal (σ : L ≃ₐ[K] L) :
    (nonZeroDivisors (Ideal (𝓞 L))) →* (nonZeroDivisors (Ideal (𝓞 L))) where
  toFun I := ⟨Ideal.map (galRingEquiv K L σ) I.val, by
    rw [mem_nonZeroDivisors_iff_ne_zero, ne_eq, ← bot_eq_zero,
      Ideal.map_eq_bot_iff_of_injective (galRingEquiv K L σ).injective,
      bot_eq_zero, ← ne_eq]
    exact mem_nonZeroDivisors_iff_ne_zero.mp I.prop⟩
  map_one' := by ext : 1; simp [Ideal.map_top]
  map_mul' := fun I J => by ext : 1; simp [Ideal.map_mul]

end GaloisClassGroupAction
end ArtinUnramified
end
