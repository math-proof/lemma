/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalCategoryDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Opposite
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence
public import Instance.v1.Atlas.TensorCategories.code.MonoidalCategoryDef

@[expose] public section

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category

universe v v₂ u u₂


namespace TensorCategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Left multiplication by the unit object is an equivalence of categories `C ⥤ C`, via
the natural isomorphism given by the left unitor. -/
@[reducible]
noncomputable def Definition_1_1_1_leftMultEquiv :
    (tensorLeft (𝟙_ C) : C ⥤ C).IsEquivalence := by
  have iso : tensorLeft (𝟙_ C) ≅ 𝟭 C := NatIso.ofComponents (fun X => λ_ X) (by simp)
  exact Functor.isEquivalence_of_iso iso.symm

/-- Right multiplication by the unit object is an equivalence of categories `C ⥤ C`, via
the natural isomorphism given by the right unitor. -/
@[reducible]
noncomputable def Definition_1_1_1_rightMultEquiv :
    (tensorRight (𝟙_ C) : C ⥤ C).IsEquivalence := by
  have iso : tensorRight (𝟙_ C) ≅ 𝟭 C := NatIso.ofComponents (fun X => ρ_ X) (by simp)
  exact Functor.isEquivalence_of_iso iso.symm

end TensorCategories
