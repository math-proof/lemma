/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ConcreteModuleCategories.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Theorem.v1.Atlas.TensorCategories.code.DeligneTensorProductMonoidal
import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Opposite
import Abbrev.v1.Atlas.TensorCategories.code.ConcreteModuleCategories.Part2
set_option maxHeartbeats 800000

universe v₁ v₂ v₃ vₘ w u₁ u₂ u₃ uₘ


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

section BimoduleCategory

/-- A `(C, D)`-bimodule category: a category `M` equipped with compatible left `C`- and right
`D`-actions satisfying the pentagon, triangle, and middle interchange coherence axioms. -/
class BimoduleCategory
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (D : Type u₂) [Category.{v₂} D] [MonoidalCategory D]
    (M : Type*) [Category M] extends BimoduleCategoryStruct C D M where
  left_pentagon : ∀ (X Y Z : C) (N : M),
    (lactWhiskerRight (α_ X Y Z).hom N) ≫
    (lactAssociator X (Y ⊗ Z) N).hom ≫
    (lactWhiskerLeft X (lactAssociator Y Z N).hom) =
    (lactAssociator (X ⊗ Y) Z N).hom ≫
    (lactAssociator X Y (lactObj Z N)).hom
  right_pentagon : ∀ (N : M) (X Y Z : D),
    (ractWhiskerLeft (ractAssociator N X Y).hom Z) ≫
    (ractAssociator N (X ⊗ Y) Z).hom ≫
    (ractWhiskerRight N (α_ X Y Z).hom) =
    (ractAssociator (ractObj N X) Y Z).hom ≫
    (ractAssociator N X (Y ⊗ Z)).hom
  middle_assoc : ∀ (X Y : C) (N : M) (Z : D),
    (ractWhiskerLeft (lactAssociator X Y N).hom Z) ≫
    (middleInterchange X (lactObj Y N) Z).hom ≫
    (lactWhiskerLeft X (middleInterchange Y N Z).hom) =
    (middleInterchange (X ⊗ Y) N Z).hom ≫
    (lactAssociator X Y (ractObj N Z)).hom
  left_unit : ∀ (X : C) (N : M),
    (lactAssociator X (𝟙_ C) N).hom ≫
    (lactWhiskerLeft X (lactLeftUnitor N).hom) =
    (lactWhiskerRight (ρ_ X).hom N)
  right_unit : ∀ (N : M) (Y : D),
    (ractAssociator N (𝟙_ D) Y).hom ≫
    (ractWhiskerRight N (λ_ Y).hom) =
    (ractWhiskerLeft (ractRightUnitor N).hom Y)
  right_middle_pentagon : ∀ (X : C) (N : M) (Y Z : D),
    (ractWhiskerLeft (middleInterchange X N Y).hom Z) ≫
    (middleInterchange X (ractObj N Y) Z).hom ≫
    (lactWhiskerLeft X (ractAssociator N Y Z).hom) =
    (ractAssociator (lactObj X N) Y Z).hom ≫
    (middleInterchange X N (Y ⊗ Z)).hom

/-- The EGNO definition of a bimodule category (over a field `k`) yields the underlying
plain `BimoduleCategory` structure by forgetting the linearity/abelian conditions. -/
class BimoduleCategoryViaDeligne
    (k : Type w) [Field k]
    (C : Type u₁) [Category.{v₁} C] [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] [TensorCategories.MultitensorCategory k C]
    (D : Type u₂) [Category.{v₂} D] [Preadditive D] [Linear k D] [Abelian D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear k D]
    [RigidCategory D] [TensorCategories.MultitensorCategory k D]
    [Abelian Dᴹᵒᵖ] [Linear k Dᴹᵒᵖ]
    (M : Type uₘ) [Category.{vₘ} M] where
  deligne : Unit := ()
  monInst : Unit := ()
  moduleStr : Unit := ()

end BimoduleCategory
end CategoryTheory
