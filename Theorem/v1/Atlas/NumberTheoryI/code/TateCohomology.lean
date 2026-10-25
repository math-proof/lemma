/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Def.v1.Atlas.NumberTheoryI.code.Cor2328
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Cor2328
import Def.v1.Atlas.NumberTheoryI.code.TateCohomology.Part4


noncomputable section

universe u

namespace TateCohomology

open Finset CategoryTheory

variable {k : Type u} [CommRing k] {G : Type u} [Group G] [Fintype G]

lemma invEquivTrivInt_apply {G₀ : Type} [Group G₀] [Fintype G₀]
    (x : (Rep.trivial ℤ G₀ ℤ).ρ.invariants) :
    (invEquivTrivInt (G₀ := G₀)) x = x.1 := by
  simp [invEquivTrivInt, Submodule.topEquiv]

lemma map_normImage_trivInt {G₀ : Type} [Group G₀] [Fintype G₀] :
    Submodule.map (invEquivTrivInt (G₀ := G₀)).toLinearMap
      (normImageInInvariants (Rep.trivial ℤ G₀ ℤ)) =
      Submodule.span ℤ {(Fintype.card G₀ : ℤ)} := by
  ext n; simp only [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [show invEquivTrivInt.toLinearMap x = x.1 from invEquivTrivInt_apply x]
    simp only [normImageInInvariants, normMap, Submodule.mem_comap,
      Submodule.coe_subtype, LinearMap.mem_range] at hx
    obtain ⟨m, hm⟩ := hx
    rw [Submodule.mem_span_singleton]
    simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply,
      Representation.trivial_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hm
    exact ⟨m, by rw [smul_eq_mul, ← hm]; ring⟩
  · intro hn
    rw [Submodule.mem_span_singleton] at hn
    obtain ⟨c, hc⟩ := hn; rw [smul_eq_mul] at hc
    refine ⟨⟨n, by rw [Representation.mem_invariants]; intro g; simp⟩, ?_, ?_⟩
    · simp only [normImageInInvariants, normMap, Submodule.mem_comap,
        Submodule.coe_subtype, LinearMap.mem_range]
      refine ⟨c, ?_⟩
      simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply,
        Representation.trivial_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      linarith
    · exact invEquivTrivInt_apply _

end TateCohomology
end
