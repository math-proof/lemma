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
import Def.v1.Atlas.NumberTheoryI.code.TateCohomology.Part6


noncomputable section

universe u

namespace TateCohomology

open Finset CategoryTheory

variable {k : Type u} [CommRing k] {G : Type u} [Group G] [Fintype G]

lemma invEquivTrivFinFun_apply {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ)
    (x : (Rep.trivial ℤ G₀ (Fin n → ℤ)).ρ.invariants) :
    (invEquivTrivFinFun n (G₀ := G₀)) x = x.1 := by
  simp [invEquivTrivFinFun, Submodule.topEquiv]

lemma map_normImage_trivFinFun {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ) :
    Submodule.map (invEquivTrivFinFun n (G₀ := G₀)).toLinearMap
      (normImageInInvariants (Rep.trivial ℤ G₀ (Fin n → ℤ))) =
      LinearMap.range ((Fintype.card G₀ : ℤ) • LinearMap.id (R := ℤ) (M := Fin n → ℤ)) := by
  ext f
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [show (invEquivTrivFinFun n).toLinearMap x = x.1 from invEquivTrivFinFun_apply n x]
    simp only [normImageInInvariants, normMap, Submodule.mem_comap,
      Submodule.coe_subtype, LinearMap.mem_range] at hx
    obtain ⟨m, hm⟩ := hx
    refine ⟨m, ?_⟩
    ext i
    simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply,
      Representation.trivial_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hm ⊢
    exact congr_fun hm i
  · rintro ⟨c, rfl⟩
    have hmem : (↑(Fintype.card G₀) : ℤ) • c ∈ (Rep.trivial ℤ G₀ (Fin n → ℤ)).ρ.invariants := by
      rw [Representation.mem_invariants]; intro g; simp
    refine ⟨⟨(↑(Fintype.card G₀) : ℤ) • c, hmem⟩, ?_, ?_⟩
    · simp only [normImageInInvariants, normMap, Submodule.mem_comap,
        Submodule.coe_subtype, LinearMap.mem_range]
      refine ⟨c, ?_⟩
      ext i
      simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply,
        Representation.trivial_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Pi.smul_apply, smul_eq_mul]
    · exact invEquivTrivFinFun_apply n _

lemma range_smul_id_eq_pi {G₀ : Type} [Group G₀] [Fintype G₀] (n : ℕ) :
    LinearMap.range ((Fintype.card G₀ : ℤ) • LinearMap.id (R := ℤ) (M := Fin n → ℤ)) =
    Submodule.pi Set.univ (fun _ : Fin n => Submodule.span ℤ {(Fintype.card G₀ : ℤ)}) := by
  ext f
  simp only [LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul,
    Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨g, rfl⟩ i
    exact ⟨g i, by simp [Pi.smul_apply, mul_comm]⟩
  · intro h
    choose c hc using h
    exact ⟨c, by ext i; simp only [Pi.smul_apply, smul_eq_mul]; linarith [hc i]⟩

end TateCohomology
end
