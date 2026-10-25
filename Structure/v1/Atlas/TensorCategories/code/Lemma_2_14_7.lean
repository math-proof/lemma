/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Lemma_2_14_7.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_
import Def.v1.Atlas.TensorCategories.code.Lemma_2_14_7
set_option linter.unusedSimpArgs false

universe u v

open CategoryTheory MonoidalCategory


namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

open HasLeftDual HasRightDual ExactPairing MonObj

namespace Lemma2147

/-- A left module object over an algebra `B` in `C`: an object `Y` equipped with an action
`B ⊗ Y ⟶ Y` satisfying the usual unit and associativity axioms. -/
structure LeftModObj (B : C) [MonObj B] (Y : C) where
  act : B ⊗ Y ⟶ Y
  act_one : (λ_ Y).inv ≫ (MonObj.one ▷ Y) ≫ act = 𝟙 Y
  act_assoc : (α_ B B Y).hom ≫ (B ◁ act) ≫ act = (MonObj.mul ▷ Y) ≫ act

/-- A right module object over an algebra `B` in `C`: an object `Y` equipped with an action
`Y ⊗ B ⟶ Y` satisfying the usual unit and associativity axioms. -/
structure RightModObj (B : C) [MonObj B] (Y : C) where
  act : Y ⊗ B ⟶ Y
  act_one : (ρ_ Y).inv ≫ (Y ◁ MonObj.one) ≫ act = 𝟙 Y
  act_assoc : (α_ Y B B).inv ≫ (act ▷ B) ≫ act = (Y ◁ MonObj.mul) ≫ act

end Lemma2147
end CategoryTheory
