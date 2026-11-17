/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/UnitSemisimplicity/UnitSimple.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Instance.v1.Atlas.TensorCategories.code.UnitSemisimplicity.TensorExactness
public import Lemma.Category.Atlas.v1.TensorCategories.code.UnitSemisimplicity.TensorExactness
public import Def.v1.Atlas.TensorCategories.code.UnitSemisimplicity.UnitSimple
open CategoryTheory MonoidalCategory Category CategoryTheory.Limits

universe v u w


public noncomputable section

namespace TensorCategories

/-- Predicate asserting that the unit object `𝟙_ C` decomposes as a finite biproduct
of pairwise non-isomorphic simple objects — the content of Theorem 1.15.8 (ii). -/
structure UnitIsSemisimple (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [HasZeroMorphisms C] : Prop where
  semisimple : ∃ (n : ℕ) (f : Fin n → C) (hbp : HasBiproduct f),
    (∀ i, Simple (f i)) ∧
    (∀ i j, i ≠ j → ¬Nonempty (f i ≅ f j)) ∧
    Nonempty (𝟙_ C ≅ @biproduct _ _ _ _ f hbp)

end TensorCategories
end
