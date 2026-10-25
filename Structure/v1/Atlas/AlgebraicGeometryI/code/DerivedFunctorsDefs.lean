/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DerivedFunctorsDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.RightDerived
set_option maxHeartbeats 800000


noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace DerivedFunctorsDefs

variable (C : Type u) [Category.{v} C] [Abelian C]
         (D : Type*) [Category D] [Abelian D]

/-- A cohomological δ-functor (Definition 43, Lecture 22–23): a sequence of additive functors
`T n : C ⥤ D` together with connecting morphisms `δ` and the long-exact-sequence and
naturality data attached to each short exact sequence in `C`. -/
structure CohomDeltaFunctor where
  T : ℕ → C ⥤ D
  additive : ∀ n, (T n).Additive
  leftExact : PreservesFiniteLimits (T 0)
  δ : ∀ (n : ℕ) (S : ShortComplex C), S.ShortExact →
    ((T n).obj S.X₃ ⟶ (T (n + 1)).obj S.X₁)
  exact_middle : ∀ (n : ℕ) (S : ShortComplex C) (_ : S.ShortExact),
    (ShortComplex.mk ((T n).map S.f) ((T n).map S.g)
      (by rw [← Functor.map_comp, S.zero, Functor.map_zero])).Exact
  comp_δ_zero : ∀ (n : ℕ) (S : ShortComplex C) (hS : S.ShortExact),
    (T n).map S.g ≫ δ n S hS = 0
  δ_comp_zero : ∀ (n : ℕ) (S : ShortComplex C) (hS : S.ShortExact),
    δ n S hS ≫ (T (n + 1)).map S.f = 0
  exact_right : ∀ (n : ℕ) (S : ShortComplex C) (hS : S.ShortExact),
    (ShortComplex.mk ((T n).map S.g) (δ n S hS) (comp_δ_zero n S hS)).Exact
  exact_left : ∀ (n : ℕ) (S : ShortComplex C) (hS : S.ShortExact),
    (ShortComplex.mk (δ n S hS) ((T (n + 1)).map S.f) (δ_comp_zero n S hS)).Exact
  δ_natural : ∀ (n : ℕ) (S S' : ShortComplex C) (hS : S.ShortExact) (hS' : S'.ShortExact)
    (φ : S ⟶ S'),
    (T n).map φ.τ₃ ≫ δ n S' hS' = δ n S hS ≫ (T (n + 1)).map φ.τ₁

variable {C D}

/-- A morphism of cohomological δ-functors `F ⟶ G` is a sequence of natural transformations
`η n : F.T n ⟶ G.T n` compatible with the connecting maps `δ` of `F` and `G`. -/
structure CohomDeltaFunctor.Morphism (F G : CohomDeltaFunctor C D) where
  η : ∀ n, F.T n ⟶ G.T n
  comm_δ : ∀ (n : ℕ) (S : ShortComplex C) (hS : S.ShortExact),
    (η n).app S.X₃ ≫ G.δ n S hS = F.δ n S hS ≫ (η (n + 1)).app S.X₁

/-- The universal property defining a derived functor (Definition 44–45, Lecture 22–23):
a δ-functor `F` is universal if every degree-zero natural transformation `F.T 0 ⟶ G.T 0`
extends uniquely to a morphism of δ-functors. -/
structure CohomDeltaFunctor.IsUniversal (F : CohomDeltaFunctor C D) : Prop where
  extend : ∀ (G : CohomDeltaFunctor C D) (η₀ : F.T 0 ⟶ G.T 0),
    ∃ (m : F.Morphism G), m.η 0 = η₀
  unique : ∀ (G : CohomDeltaFunctor C D) (m₁ m₂ : F.Morphism G),
    m₁.η 0 = m₂.η 0 → ∀ n, m₁.η n = m₂.η n

end DerivedFunctorsDefs
end
