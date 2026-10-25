/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleRigidityCompat.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Abbrev.v1.Atlas.TensorCategories.code.ModuleRigidityCompat
set_option maxHeartbeats 800000

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

namespace ExactModuleCategory

open Category MonoidalCategory LeftModCat

section Construction

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [LeftRigidCategory C]
         {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]
         [hMEC : ModuleEvalCoeval C M]

/-- A `ModuleEvalCoeval` structure on `(C, M)` produces a `ModuleRigidityCompat` instance,
using the supplied evaluation/coevaluation and zigzag identities. -/
noncomputable instance ofEvalCoeval :
    ModuleRigidityCompat C M where
  modRigidForward P N A f :=
    (ᘁP : C) ◁ᵐ f ≫ (actμ_ (ᘁP : C) P N).inv ≫
      (ev P) ▷ᵐ N ≫ (actℓ_ N).hom
  modRigidBackward P N A g :=
    (actℓ_ A).inv ≫ (coev P) ▷ᵐ A ≫
      (actμ_ P (ᘁP : C) A).hom ≫ P ◁ᵐ g
  modRigid_left_inv P N A g := hMEC.zigzag_left P N A g
  modRigid_right_inv P N A f := hMEC.zigzag_right P N A f
  modRigidForward_natural P N e g := by
    intro e' g'
    rw [actWhiskerLeft_comp, assoc]

end Construction
end ExactModuleCategory
end CategoryTheory
