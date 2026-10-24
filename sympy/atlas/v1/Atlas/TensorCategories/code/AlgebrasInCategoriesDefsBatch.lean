/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/AlgebrasInCategoriesDefsBatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.ModuleCategory
import sympy.atlas.v1.Atlas.TensorCategories.code.ExactModuleCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Mathlib.CategoryTheory.Monoidal.Bimod
import Mathlib.CategoryTheory.Monoidal.Mod_
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

set_option maxHeartbeats 800000

universe v u

namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- An algebra in a multitensor category `C` is a triple `(A, m, u)` where `A : C` and
`m : A ⊗ A → A`, `u : 1 → A` are morphisms satisfying associativity and unit axioms.
Identified here with Mathlib's `Mon C` of monoid objects. -/
abbrev Definition_2_9_1_AlgebraInMonoidalCategory := Mon C

/-- Two algebras `A` and `B` in `C` are Morita equivalent if the module categories `Mod_C(A)`
and `Mod_C(B)` are module equivalent. Stated here directly for module categories `M₁` and `M₂`
as the existence of a module equivalence between them. -/
def Definition_2_9_18_MoritaEquivalence
    (M₁ : Type*) (M₂ : Type*)
    [Category M₁] [Category M₂]
    [LeftModuleCategory C M₁]
    [LeftModuleCategory C M₂] : Prop :=
  Nonempty (ModuleEquivalence C M₁ M₂)

/-- An algebra `A` in the category `C` is exact if the module category `Mod_C(A)` is exact. -/
def Definition_2_9_21_ExactAlgebra
    (A : C) [MonObj A]
    [LeftModuleCategory C (Mod_ C A)] : Prop :=
  Nonempty (ExactModuleCategory C (Mod_ C A))

/-- Top-level abbreviation for Definition 2.9.21: an algebra `A` in `C` is exact iff the
module category `Mod_C(A)` is exact. -/
abbrev Definition_2_9_21 := @Definition_2_9_21_ExactAlgebra C _ _

variable [Limits.HasCoequalizers C]

/-- Tensor product over an algebra `A`: for a right `A`-module `(M, actR)` and a left
`A`-module `(N, actL)`, the object `M ⊗_A N` is the coequalizer of the two natural maps
`M ⊗ A ⊗ N ⇒ M ⊗ N` induced by the two actions. -/
noncomputable def Definition_2_9_22_TensorOverAlgebra
    {A M N : C} (actR : M ⊗ A ⟶ M) (actL : A ⊗ N ⟶ N) : C :=
  Limits.coequalizer
    ((α_ M A N).inv ≫ (actR ▷ N))
    (M ◁ actL)

/-- An `A`-`B`-bimodule in a monoidal category `C` is a triple `(M, p, q)` consisting of an
object `M ∈ C`, a left `A`-action `p : A ⊗ M → M`, and a right `B`-action `q : M ⊗ B → M`
that commute appropriately. Implemented via Mathlib's `Bimod A B`. -/
abbrev Definition_2_9_24_BimoduleInMonoidalCategory (A B : Mon C) := Bimod A B

end CategoryTheory
