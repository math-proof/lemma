/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Abbrev.v1.Atlas.TensorCategories.code.IndecomposableModuleCat
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_
import Def.v1.Atlas.TensorCategories.code.DualCategory.Part10
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

variable (M : Type u) [Category.{v} M] [LeftModuleCategory C M]

namespace DualCatObj

variable {C M}

attribute [reassoc] Hom.comm

section Lemma_2_14_7

open MonObj in
/-- A left module over an algebra object `B ∈ C`: an object `Y` together with an action
`B ⊗ Y ⟶ Y` satisfying the usual unit and associativity axioms. -/
structure LeftModObj (B : C) [MonObj B] (Y : C) where
  act : B ⊗ Y ⟶ Y
  act_one : (λ_ Y).inv ≫ (MonObj.one ▷ Y) ≫ act = 𝟙 Y
  act_assoc : (α_ B B Y).hom ≫ (B ◁ act) ≫ act = (MonObj.mul ▷ Y) ≫ act

open MonObj in
/-- A right module over an algebra object `B ∈ C`: an object `Y` together with an
action `Y ⊗ B ⟶ Y` satisfying the usual unit and associativity axioms. -/
structure RightModObj (B : C) [MonObj B] (Y : C) where
  act : Y ⊗ B ⟶ Y
  act_one : (ρ_ Y).inv ≫ (Y ◁ MonObj.one) ≫ act = 𝟙 Y
  act_assoc : (α_ Y B B).inv ≫ (act ▷ B) ≫ act = (Y ◁ MonObj.mul) ≫ act

/-- Theorem 2.11.2 (essential surjectivity, left version): every left `A`-module is
isomorphic to one of the form `F N` for some `N ∈ C`. -/

end Lemma_2_14_7

/-- Lemma 2.14.7: classification of left and right `(ᘁA ⊗ A)`-modules in terms of
tensor products with `ᘁA` or `A`. -/

end DualCatObj

/-- The enveloping monoidal category `C ⊠ C^{op}` of a monoidal category `C`. -/
structure DrinfeldCenterHalfBraidingObj (C : Type u) [Category.{v} C] [MonoidalCategory C] where
  X : C
  halfBraiding : ∀ (V : C), (V ⊗ X) ≅ (X ⊗ V)
  halfBraiding_natural : ∀ {V₁ V₂ : C} (f : V₁ ⟶ V₂),
    (f ▷ X) ≫ (halfBraiding V₂).hom = (halfBraiding V₁).hom ≫ (X ◁ f)
  halfBraiding_tensor : ∀ (V W : C),
    (halfBraiding (V ⊗ W)).hom =
      (α_ V W X).hom ≫ (V ◁ (halfBraiding W).hom) ≫ (α_ V X W).inv ≫
        ((halfBraiding V).hom ▷ W) ≫ (α_ X V W).hom

/-- A morphism between half-braiding objects of the Drinfeld center: a morphism of the
underlying objects compatible with the half-braiding isomorphisms. -/
structure DrinfeldCenterHalfBraidingHom {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (P Q : DrinfeldCenterHalfBraidingObj C) where
  hom : P.X ⟶ Q.X
  comm : ∀ (V : C),
    (V ◁ hom) ≫ (Q.halfBraiding V).hom = (P.halfBraiding V).hom ≫ (hom ▷ V)

end CategoryTheory
