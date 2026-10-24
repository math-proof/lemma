/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorHomEquivHelper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory


namespace CategoryTheory

section NaturalityVerification

variable {C : Type*} [Category C] [MonoidalCategory C]

example {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X ⊗ Y ⟶ Z) (g : Z ⟶ Z') :
    (tensorRightHomEquiv X Y Y' Z') (f ≫ g) =
      (tensorRightHomEquiv X Y Y' Z) f ≫ g ▷ Y' :=
  tensorRightHomEquiv_naturality f g

example {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : Y' ⊗ X ⟶ Z) (g : Z ⟶ Z') :
    (tensorLeftHomEquiv X Y Y' Z') (f ≫ g) =
      (tensorLeftHomEquiv X Y Y' Z) f ≫ Y ◁ g :=
  tensorLeftHomEquiv_naturality f g

example {X X' Y Y' Z : C} [ExactPairing Y Y'] (f : X ⟶ X') (g : X' ⟶ Z ⊗ Y') :
    (tensorRightHomEquiv X Y Y' Z).symm (f ≫ g) =
      f ▷ Y ≫ (tensorRightHomEquiv X' Y Y' Z).symm g :=
  tensorRightHomEquiv_symm_naturality f g

example {X X' Y Y' Z : C} [ExactPairing Y Y'] (f : X ⟶ X') (g : X' ⟶ Y ⊗ Z) :
    (tensorLeftHomEquiv X Y Y' Z).symm (f ≫ g) =
      _ ◁ f ≫ (tensorLeftHomEquiv X' Y Y' Z).symm g :=
  tensorLeftHomEquiv_symm_naturality f g

end NaturalityVerification

end CategoryTheory


namespace TensorCategories

open CategoryTheory

section NaturalityVerification

variable {C : Type*} [Category C] [MonoidalCategory C]

example {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : X ⊗ Y ⟶ Z) (g : Z ⟶ Z') :
    (tensorRightHomEquiv X Y Y' Z') (f ≫ g) =
      (tensorRightHomEquiv X Y Y' Z) f ≫ g ▷ Y' :=
  tensorRightHomEquiv_naturality f g

example {X Y Y' Z Z' : C} [ExactPairing Y Y'] (f : Y' ⊗ X ⟶ Z) (g : Z ⟶ Z') :
    (tensorLeftHomEquiv X Y Y' Z') (f ≫ g) =
      (tensorLeftHomEquiv X Y Y' Z) f ≫ Y ◁ g :=
  tensorLeftHomEquiv_naturality f g

end NaturalityVerification

end TensorCategories
