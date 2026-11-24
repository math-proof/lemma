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
public import Def.v1.Atlas.NumberTheoryI.code.ArtinUnramified.Part2


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

section GaloisClassGroupAction

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

set_option maxHeartbeats 800000 in
omit [FiniteDimensional K L] in
lemma mk0_mapIdealGal_congr (σ : L ≃ₐ[K] L)
    {I J : nonZeroDivisors (Ideal (𝓞 L))}
    (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    ClassGroup.mk0 (mapIdealGal K L σ I) = ClassGroup.mk0 (mapIdealGal K L σ J) := by
  rw [ClassGroup.mk0_eq_mk0_iff] at h ⊢
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  let e := galRingEquiv K L σ
  refine ⟨e x, e y, fun h0 => hx (e.injective (by rwa [map_zero])),
    fun h0 => hy (e.injective (by rwa [map_zero])), ?_⟩
  show Ideal.span {e x} * Ideal.map e ↑I = Ideal.span {e y} * Ideal.map e ↑J
  rw [show Ideal.span {e x} = Ideal.map e (Ideal.span {x}) from
    by rw [Ideal.map_span]; simp [Set.image_singleton],
   show Ideal.span {e y} = Ideal.map e (Ideal.span {y}) from
    by rw [Ideal.map_span]; simp [Set.image_singleton],
   ← Ideal.map_mul, ← Ideal.map_mul, hxy]

end GaloisClassGroupAction
end ArtinUnramified
end
