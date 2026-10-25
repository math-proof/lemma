/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SemisimpleMultitensor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Structure.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.PivotalSpherical
import Def.v1.Atlas.TensorCategories.code.SemisimpleMultitensor.Part4
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v u


noncomputable section

namespace CategoryTheory

section UnitSemisimple

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

section ComponentSubcategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

section RigidDuals

variable [RigidCategory C]

/-- The right adjoint mate of any endomorphism of the unit `𝟙_ C` equals the endomorphism itself,
since the unit is canonically self-dual in a rigid category. -/
theorem rightAdjointMate_unit_endo (g : 𝟙_ C ⟶ 𝟙_ C) :
    rightAdjointMate g = g := by
  show (ρ_ (𝟙_ C)).inv ≫ (𝟙_ C) ◁ (ρ_ (𝟙_ C)).inv ≫ (𝟙_ C) ◁ g ▷ (𝟙_ C) ≫
    (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).inv ≫ (ρ_ (𝟙_ C)).hom ▷ (𝟙_ C) ≫ (λ_ (𝟙_ C)).hom = g
  calc _ = 𝟙 _ ⊗≫ (𝟙_ C) ◁ g ▷ (𝟙_ C) ⊗≫ 𝟙 _ := by monoidal
       _ = g := by monoidal

end RigidDuals
end ComponentSubcategories
end UnitSemisimple
end CategoryTheory
end
