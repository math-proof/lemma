/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Definition_2_9_22.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Mod_
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

set_option maxHeartbeats 400000

universe v u

namespace CategoryTheory

open Category MonoidalCategory MonObj Limits

section TensorOverAlgebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [HasCoequalizers C]

/-- Definition 2.9.22: the tensor product `M ⊗_A N` of a right `A`-module `M` and a
left `A`-module `N`, constructed as the coequalizer of the two natural maps
`M ⊗ A ⊗ N ⇒ M ⊗ N`. -/
noncomputable def Definition_2_9_22_TensorOverAlgebra
    {A M N : C} (actR : M ⊗ A ⟶ M) (actL : A ⊗ N ⟶ N) : C :=
  coequalizer
    ((α_ M A N).inv ≫ (actR ▷ N))
    (M ◁ actL)

/-- Alias of `Definition_2_9_22_TensorOverAlgebra`: the relative tensor product
`M ⊗_A N`. -/
noncomputable abbrev Definition_2_9_22
    {A M N : C} (actR : M ⊗ A ⟶ M) (actL : A ⊗ N ⟶ N) : C :=
  Definition_2_9_22_TensorOverAlgebra actR actL

end TensorOverAlgebra

section SimpleAndSemisimple

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- An algebra object `A ∈ C` is semisimple when its category of modules is
preadditive and every module decomposes as a biproduct of simple modules. -/
def IsSemisimpleAlgebra (A : C) [MonObj A] : Prop :=
  ∃ (hp : Preadditive (Mod_ C A)),
    let hz : HasZeroMorphisms (Mod_ C A) :=
      @Preadditive.preadditiveHasZeroMorphisms _ _ hp
    ∀ (X : Mod_ C A), ∃ (n : ℕ) (Y : Fin n → Mod_ C A)
      (_ : ∀ i, @Simple (Mod_ C A) _ hz (Y i))
      (_ : @HasBiproduct (Fin n) (Mod_ C A) _ hz Y),
      Nonempty (X ≅ @biproduct (Fin n) (Mod_ C A) _ hz Y _)

/-- An algebra object `A ∈ C` is simple when its category of modules has a unique
simple object up to isomorphism. -/
def IsSimpleAlgebra (A : C) [MonObj A] : Prop :=
  ∃ (hz : HasZeroMorphisms (Mod_ C A)) (S : Mod_ C A) (_ : @Simple (Mod_ C A) _ hz S),
    ∀ (X : Mod_ C A), @Simple (Mod_ C A) _ hz X → Nonempty (X ≅ S)

end SimpleAndSemisimple

end CategoryTheory
