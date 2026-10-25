/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_15_5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.SemisimpleMultitensor.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.SemisimpleMultitensor
open CategoryTheory MonoidalCategory Limits

universe u v


/-- Proposition 1.15.5: package of conclusions about a multiring category given a
decomposition `𝟙_ C ≅ ⨁ f` of the unit into simple objects: every object decomposes into
components `componentObj f X i j`, tensor products vanish off the diagonal, are compatible
on the diagonal, and right/left duals swap the indices. -/
structure Proposition_1_15_5
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] [HasFiniteBiproducts C] [RigidCategory C]
    {n : ℕ} (f : Fin n → C) [HasBiproduct f]
    (hiso : 𝟙_ C ≅ ⨁ f) (hsimp : ∀ i, Simple (f i)) : Prop where
  decomposition : ∀ (X : C),
    ∃ (_ : HasBiproduct (componentFamily f X)),
      Nonempty (X ≅ ⨁ (componentFamily f X))
  tensor_zero : ∀ (X Y : C) (i j k l : Fin n), j ≠ k →
    IsZero (componentObj f X i j ⊗ componentObj f Y k l)
  tensor_compatible : ∀ (X Y : C) (i j l : Fin n),
    Nonempty (componentObj f X i j ⊗ componentObj f Y j l ≅ componentObj f ((X ⊗ f j) ⊗ Y) i l)
  rightDual_maps : ∀ (X : C) (i j : Fin n),
    Nonempty ((componentObj f X i j)ᘁ ≅ componentObj f (Xᘁ) j i)
  leftDual_maps : ∀ (X : C) (i j : Fin n),
    Nonempty ((ᘁ(componentObj f X i j) : C) ≅ componentObj f (ᘁX : C) j i)

