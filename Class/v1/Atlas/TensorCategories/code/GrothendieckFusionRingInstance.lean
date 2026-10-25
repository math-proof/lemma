/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckFusionRingInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRingCategorical
import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part4
open CategoryTheory MonoidalCategory Finset

universe v u


namespace CategoryTheory

/-- Typeclass packaging Jordan-Hölder multiplicities for a rigid linear monoidal abelian
category `C` with categorical fusion data: each object is assigned multiplicities
indexed by the simples in a way compatible with the unit, tensor product and isomorphisms. -/
class HasJordanHolderMultiplicities
    (κ : Type*) [Field κ] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear κ C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear κ C]
    [RigidCategory C]
    [cfd : CategoricalFusionData κ C] where
  mult : C → cfd.ι → ℕ
  mult_simple : ∀ i j, mult (cfd.S i) j = if i = j then 1 else 0
  mult_unit : ∀ j, mult (𝟙_ C) j = if j = cfd.unitIdx then 1 else 0
  mult_tensor : ∀ (X Y : C) (l : cfd.ι),
    mult (X ⊗ Y) l = ∑ i : cfd.ι, ∑ j : cfd.ι, mult X i * mult Y j * cfd.N i j l
  mult_iso : ∀ (X Y : C), Nonempty (X ≅ Y) → ∀ i, mult X i = mult Y i
  mult_nontrivial : ∀ (X : C), ∃ i, 0 < mult X i

end CategoryTheory
