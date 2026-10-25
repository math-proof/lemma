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
import Def.v1.Atlas.NumberTheoryI.code.ArtinUnramified.Part3


noncomputable section

open scoped Pointwise

open NumberField

namespace ArtinUnramified

section GaloisClassGroupAction

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

set_option maxHeartbeats 800000 in
omit [FiniteDimensional K L] in
lemma actOnClassGroup_mk0 (σ : L ≃ₐ[K] L)
    (I : nonZeroDivisors (Ideal (𝓞 L))) :
    actOnClassGroup K L σ (ClassGroup.mk0 I) =
    ClassGroup.mk0 (mapIdealGal K L σ I) :=
  mk0_mapIdealGal_congr K L σ
    (Function.surjInv_eq ClassGroup.mk0_surjective (ClassGroup.mk0 I))

set_option maxHeartbeats 1600000 in
omit [FiniteDimensional K L] in
lemma actOnClassGroup_mul (σ τ : L ≃ₐ[K] L) :
    actOnClassGroup K L (σ * τ) =
    (actOnClassGroup K L σ).comp (actOnClassGroup K L τ) := by
  ext c; obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  simp only [MonoidHom.comp_apply, actOnClassGroup_mk0]; congr 1; ext : 1
  show Ideal.map (galRingEquiv K L (σ * τ)) I.val =
    Ideal.map (galRingEquiv K L σ) (Ideal.map (galRingEquiv K L τ) I.val)
  rw [ideal_map_comp_ringEquiv, galRingEquiv_mul]

set_option maxHeartbeats 1600000 in
omit [FiniteDimensional K L] in
lemma actOnClassGroup_one :
    actOnClassGroup K L 1 = MonoidHom.id _ := by
  ext c; obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  simp only [MonoidHom.id_apply, actOnClassGroup_mk0]; congr 1; ext : 1
  show Ideal.map (galRingEquiv K L 1) I.val = I.val
  rw [galRingEquiv_one, ideal_map_refl_ringEquiv]

end GaloisClassGroupAction
end ArtinUnramified
end
