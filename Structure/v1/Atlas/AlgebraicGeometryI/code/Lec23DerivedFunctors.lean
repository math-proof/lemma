/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec23DerivedFunctors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Preserves.Finite
set_option maxHeartbeats 800000

open CategoryTheory Category Limits


noncomputable section

universe v u

namespace Lec23

/-- A δ-functor `T = (Tⁿ)_{n ≥ 0} : A → B`: additive functors with `T⁰` left exact and
natural connecting homomorphisms `δⁿ` fitting into long exact sequences for every short
exact sequence of `A`. -/
structure DeltaFunctor (A : Type u) [Category.{v} A] [Abelian A]
    (B : Type*) [Category B] [Abelian B] where
  T : ℕ → (A ⥤ B)
  additive : ∀ n, (T n).Additive
  leftExact : PreservesFiniteLimits (T 0)
  δ : ∀ (n : ℕ) (S : ShortComplex A), S.ShortExact →
    ((T n).obj S.X₃ ⟶ (T (n + 1)).obj S.X₁)
  δ_comp : ∀ (n : ℕ) (S : ShortComplex A) (hS : S.ShortExact),
    δ n S hS ≫ (T (n + 1)).map S.f = 0
  comp_δ : ∀ (n : ℕ) (S : ShortComplex A) (hS : S.ShortExact),
    (T n).map S.g ≫ δ n S hS = 0
  exact₁ : ∀ (n : ℕ) (S : ShortComplex A) (hS : S.ShortExact),
    (ShortComplex.mk (δ n S hS) ((T (n + 1)).map S.f) (δ_comp n S hS)).Exact
  exact₂ : ∀ (n : ℕ) (S : ShortComplex A) (_hS : S.ShortExact),
    (ShortComplex.mk ((T n).map S.f) ((T n).map S.g)
      (by rw [← Functor.map_comp, S.zero, Functor.map_zero])).Exact
  exact₃ : ∀ (n : ℕ) (S : ShortComplex A) (hS : S.ShortExact),
    (ShortComplex.mk ((T n).map S.g) (δ n S hS) (comp_δ n S hS)).Exact
  δ_natural : ∀ (n : ℕ) (S S' : ShortComplex A) (hS : S.ShortExact) (hS' : S'.ShortExact)
    (φ : S ⟶ S'),
    (T n).map φ.τ₃ ≫ δ n S' hS' = δ n S hS ≫ (T (n + 1)).map φ.τ₁

attribute [instance] DeltaFunctor.additive

/-- A δ-functor `T` is universal if every natural transformation `S⁰ → T⁰` from another
δ-functor extends to a unique morphism of δ-functors `S → T`. -/
structure IsUniversalDeltaFunctor {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type*} [Category B] [Abelian B]
    (T : DeltaFunctor A B) : Prop where
  exists_hom : ∀ (S : DeltaFunctor A B) (η₀ : S.T 0 ⟶ T.T 0),
    ∃ (η : ∀ n, S.T n ⟶ T.T n),
      η 0 = η₀ ∧
      ∀ (n : ℕ) (SC : ShortComplex A) (hSC : SC.ShortExact),
        (η n).app SC.X₃ ≫ T.δ n SC hSC = S.δ n SC hSC ≫ (η (n + 1)).app SC.X₁
  unique : ∀ (S : DeltaFunctor A B) (η₀ : S.T 0 ⟶ T.T 0)
    (η η' : ∀ n, S.T n ⟶ T.T n),
    η 0 = η₀ → η' 0 = η₀ →
    (∀ (n : ℕ) (SC : ShortComplex A) (hSC : SC.ShortExact),
        (η n).app SC.X₃ ≫ T.δ n SC hSC = S.δ n SC hSC ≫ (η (n + 1)).app SC.X₁) →
    (∀ (n : ℕ) (SC : ShortComplex A) (hSC : SC.ShortExact),
        (η' n).app SC.X₃ ≫ T.δ n SC hSC = S.δ n SC hSC ≫ (η' (n + 1)).app SC.X₁) →
    ∀ n, η n = η' n

end Lec23
end
