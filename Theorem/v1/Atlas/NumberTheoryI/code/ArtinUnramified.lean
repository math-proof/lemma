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
import Def.v1.Atlas.NumberTheoryI.code.ArtinUnramified


noncomputable section

open scoped Pointwise

open NumberField

namespace ArtinUnramified

section GaloisClassGroupAction

lemma ideal_map_comp_ringEquiv {R : Type*} [CommRing R]
    (e₁ e₂ : R ≃+* R) (I : Ideal R) :
    Ideal.map e₂ (Ideal.map e₁ I) = Ideal.map (e₁.trans e₂) I := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr; intro x hx
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective e₁ e₁.surjective).mp hx
    exact Ideal.mem_map_of_mem _ hy
  · apply Ideal.map_le_iff_le_comap.mpr; intro x hx
    exact Ideal.mem_map_of_mem e₂ (Ideal.mem_map_of_mem e₁ hx)

lemma ideal_map_refl_ringEquiv {R : Type*} [CommRing R] (I : Ideal R) :
    Ideal.map (RingEquiv.refl R) I = I := by
  apply le_antisymm
  · exact Ideal.map_le_iff_le_comap.mpr (fun x hx => by simpa using hx)
  · exact fun x hx => Ideal.mem_map_of_mem _ hx

end GaloisClassGroupAction
end ArtinUnramified
end
