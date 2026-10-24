/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalUnitProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence

set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Category

universe v u

namespace TensorCategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- An abstract characterisation of a unit object `U`: it admits natural isomorphisms
exhibiting `tensorRight U` and `tensorLeft U` as the identity functor, and these satisfy
a triangle-type compatibility. -/
structure IsUnitObject (U : C) where
  rightUnitor' : tensorRight U ≅ Functor.id C
  leftUnitor' : tensorLeft U ≅ Functor.id C
  triangle' : ∀ (X Y : C),
    (α_ X U Y).hom ≫ X ◁ (leftUnitor'.hom.app Y) = (rightUnitor'.hom.app X) ▷ Y

/-- The canonical unit object `𝟙_ C` satisfies `IsUnitObject`, with the unitors as its
distinguished natural isomorphisms. -/
noncomputable def unitIsUnitObject : IsUnitObject (𝟙_ C) where
  rightUnitor' := NatIso.ofComponents (fun X => ρ_ X) (by aesop_cat)
  leftUnitor' := NatIso.ofComponents (fun X => λ_ X) (by aesop_cat)
  triangle' := fun X Y => by simp [NatIso.ofComponents]

/-- Construction of an isomorphism `𝟙_ C ≅ U` for any object `U` satisfying
`IsUnitObject`. -/
noncomputable def unit_object_iso_of_isUnit (U : C) (hU : IsUnitObject U) : 𝟙_ C ≅ U :=
  (hU.rightUnitor'.app (𝟙_ C)).symm ≪≫ (λ_ U)
