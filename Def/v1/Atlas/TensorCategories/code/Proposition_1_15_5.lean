/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_15_5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.SemisimpleMultitensor.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.SemisimpleMultitensor
import Structure.v1.Atlas.TensorCategories.code.Proposition_1_15_5
open CategoryTheory MonoidalCategory Limits

universe u v


/-- Construction witnessing Proposition 1.15.5: given a decomposition `𝟙_ C ≅ ⨁ f` of the
unit into simple objects, every object of `C` decomposes as a biproduct over the index pairs
`(i, j)`, and tensor products and duals satisfy the expected block structure. -/
noncomputable def proposition_1_15_5
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] [HasFiniteBiproducts C] [RigidCategory C]
    {n : ℕ} (f : Fin n → C) [HasBiproduct f]
    (hiso : 𝟙_ C ≅ ⨁ f) (hsimp : ∀ i, Simple (f i)) :
    Proposition_1_15_5 f hiso hsimp where
  decomposition := object_componentDecomposition f hiso hsimp
  tensor_zero X Y i j k l hjk := tensor_component_zero f hiso hsimp X Y i j k l hjk
  tensor_compatible X Y i j l := ⟨tensor_component_compatible f hiso hsimp X Y i j l⟩
  rightDual_maps X i j := ⟨rightDual_component f hiso hsimp X i j⟩
  leftDual_maps X i j := ⟨leftDual_component f hiso hsimp X i j⟩

