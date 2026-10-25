/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GroupCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Def.v1.Atlas.NumberTheoryI.code.GroupCohomology


noncomputable section

open CategoryTheory

universe u

namespace GroupCohomology

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

structure CohomologicalDeltaFunctor where
  F : ℕ → (𝒜 ⥤ ℬ)
  additive : ∀ n, (F n).Additive
  δ : ∀ (S : ShortComplex 𝒜) (_ : S.ShortExact) (n : ℕ),
    (F n).obj S.X₃ ⟶ (F (n + 1)).obj S.X₁
  map_g_comp_δ : ∀ (S : ShortComplex 𝒜) (hS : S.ShortExact) (n : ℕ),
    (F n).map S.g ≫ δ S hS n = 0
  δ_comp_map_f : ∀ (S : ShortComplex 𝒜) (hS : S.ShortExact) (n : ℕ),
    δ S hS n ≫ (F (n + 1)).map S.f = 0
  exact₂ : ∀ (S : ShortComplex 𝒜) (_ : S.ShortExact) (n : ℕ),
    (ShortComplex.mk ((F n).map S.f) ((F n).map S.g)
      (by rw [← Functor.map_comp, S.zero, Functor.map_zero])).Exact
  exact₃ : ∀ (S : ShortComplex 𝒜) (hS : S.ShortExact) (n : ℕ),
    (ShortComplex.mk ((F n).map S.g) (δ S hS n) (map_g_comp_δ S hS n)).Exact
  exact₁ : ∀ (S : ShortComplex 𝒜) (hS : S.ShortExact) (n : ℕ),
    (ShortComplex.mk (δ S hS n) ((F (n + 1)).map S.f) (δ_comp_map_f S hS n)).Exact
  δ_natural : ∀ {S T : ShortComplex 𝒜} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ),
    δ S hS n ≫ (F (n + 1)).map φ.τ₁ = (F n).map φ.τ₃ ≫ δ T hT n

structure HomologicalDeltaFunctor where
  F : ℕ → (𝒜 ⥤ ℬ)
  additive : ∀ n, (F n).Additive
  δ : ∀ (S : ShortComplex 𝒜) (_ : S.ShortExact) (n : ℕ),
    (F (n + 1)).obj S.X₃ ⟶ (F n).obj S.X₁
  map_g_comp_δ : ∀ (S : ShortComplex 𝒜) (hS : S.ShortExact) (n : ℕ),
    (F (n + 1)).map S.g ≫ δ S hS n = 0
  δ_comp_map_f : ∀ (S : ShortComplex 𝒜) (hS : S.ShortExact) (n : ℕ),
    δ S hS n ≫ (F n).map S.f = 0
  exact₂ : ∀ (S : ShortComplex 𝒜) (_ : S.ShortExact) (n : ℕ),
    (ShortComplex.mk ((F n).map S.f) ((F n).map S.g)
      (by rw [← Functor.map_comp, S.zero, Functor.map_zero])).Exact
  exact₁ : ∀ (S : ShortComplex 𝒜) (hS : S.ShortExact) (n : ℕ),
    (ShortComplex.mk (δ S hS n) ((F n).map S.f) (δ_comp_map_f S hS n)).Exact
  exact₃ : ∀ (S : ShortComplex 𝒜) (hS : S.ShortExact) (n : ℕ),
    (ShortComplex.mk ((F (n + 1)).map S.g) (δ S hS n) (map_g_comp_δ S hS n)).Exact
  δ_natural : ∀ {S T : ShortComplex 𝒜} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ),
    δ S hS n ≫ (F n).map φ.τ₁ = (F (n + 1)).map φ.τ₃ ≫ δ T hT n

end GroupCohomology
end
