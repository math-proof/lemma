/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_2_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A version of "unit object" data: an object `U` together with natural isomorphisms
identifying `tensorLeft U` and `tensorRight U` with the identity functor, and satisfying the
triangle axiom relating them via the associator. -/
structure IsUnitObject' (U : C) where
  rightUnitor' : tensorRight U ≅ Functor.id C
  leftUnitor' : tensorLeft U ≅ Functor.id C
  triangle' : ∀ (X Y : C),
    (α_ X U Y).hom ≫ X ◁ (leftUnitor'.hom.app Y) = (rightUnitor'.hom.app X) ▷ Y

/-- The canonical unit object `𝟙_ C` together with its left/right unitors satisfies the
`IsUnitObject'` predicate. -/
noncomputable def unitIsUnitObject' : IsUnitObject' (𝟙_ C) (C := C) where
  rightUnitor' := NatIso.ofComponents (fun X => ρ_ X) (by aesop_cat)
  leftUnitor' := NatIso.ofComponents (fun X => λ_ X) (by aesop_cat)
  triangle' := fun X Y => by simp [NatIso.ofComponents]

/-- For any object `U` equipped with a unit structure `hU : IsUnitObject' U`, there is a
canonical isomorphism `𝟙_ C ≅ U` constructed from the right-unitor of `hU` and the standard
left-unitor of `𝟙_ C`. -/
noncomputable def unit_object_iso' (U : C) (hU : IsUnitObject' U) : 𝟙_ C ≅ U :=
  (hU.rightUnitor'.app (𝟙_ C)).symm ≪≫ (λ_ U)
