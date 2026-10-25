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
import Theorem.v1.Atlas.NumberTheoryI.code.ArtinUnramified.Part4


noncomputable section

open scoped Pointwise

open NumberField

namespace ArtinUnramified

section GaloisClassGroupAction

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

def classGroupMulAut (σ : L ≃ₐ[K] L) : MulAut (ClassGroup (𝓞 L)) :=
  MulEquiv.ofBijective (actOnClassGroup K L σ) ⟨
    fun a b h => by
      have := congr_arg (actOnClassGroup K L σ⁻¹) h
      simp only [← MonoidHom.comp_apply,
        show (actOnClassGroup K L σ⁻¹).comp (actOnClassGroup K L σ) = MonoidHom.id _ from
          by rw [← actOnClassGroup_mul, inv_mul_cancel, actOnClassGroup_one]] at this
      exact this,
    fun b => ⟨actOnClassGroup K L σ⁻¹ b, by
      show (actOnClassGroup K L σ).comp (actOnClassGroup K L σ⁻¹) b = b
      rw [← actOnClassGroup_mul, mul_inv_cancel, actOnClassGroup_one]; rfl⟩⟩

set_option maxHeartbeats 1600000 in
def classGroupAutHom :
    (L ≃ₐ[K] L) →* MulAut (ClassGroup (𝓞 L)) where
  toFun := classGroupMulAut K L
  map_one' := by
    ext x; show (actOnClassGroup K L 1) x = x
    rw [actOnClassGroup_one]; rfl
  map_mul' σ τ := by
    ext x
    show (actOnClassGroup K L (σ * τ)) x =
      (classGroupMulAut K L σ) ((classGroupMulAut K L τ) x)
    rw [actOnClassGroup_mul]; rfl

end GaloisClassGroupAction
end ArtinUnramified
end
