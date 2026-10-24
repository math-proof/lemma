/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EffaceableUniversal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.DerivedFunctorsDefs
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.DerivedFunctorsDefs

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace DerivedFunctorsDefs

variable {C : Type u} [Category.{v} C] [Abelian C]
         {D : Type*} [Category D] [Abelian D]

/-- A cohomological δ-functor `F` is effaceable when every object `X` admits a
mono into an `I` killed by `F^{n+1}` for every `n`. -/
def CohomDeltaFunctor.IsEffaceable (F : CohomDeltaFunctor C D) : Prop :=
  ∀ (n : ℕ) (X : C), ∃ (I : C) (i : X ⟶ I), Mono i ∧ IsZero ((F.T (n + 1)).obj I)

/-- A weaker form of effaceability: every `X` admits a mono into some `I` such
that `F^{n+1}` sends `i` to zero, without requiring `F^{n+1}(I)` itself to vanish. -/
def CohomDeltaFunctor.IsEffaceableMorphism (F : CohomDeltaFunctor C D) : Prop :=
  ∀ (n : ℕ) (X : C), ∃ (I : C) (i : X ⟶ I), Mono i ∧ (F.T (n + 1)).map i = 0

/-- Pointwise effaceability: for any test morphism into `F^{n+1}(X)`, we can find
a mono `φ : X ⟶ N` after composition with which the morphism becomes zero. -/
def CohomDeltaFunctor.IsEffaceablePointwise (F : CohomDeltaFunctor C D) : Prop :=
  ∀ (n : ℕ) (X : C) (Y : D) (m : Y ⟶ (F.T (n + 1)).obj X),
    ∃ (N : C) (φ : X ⟶ N), Mono φ ∧ m ≫ (F.T (n + 1)).map φ = 0
