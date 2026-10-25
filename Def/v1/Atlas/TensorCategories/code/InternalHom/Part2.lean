/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Theorem.v1.Atlas.TensorCategories.code.InternalHom
set_option maxHeartbeats 800000

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

export HasModuleInternalHom (moduleIHom moduleIHomEquiv moduleIHomEquiv_natural)

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
    [HasModuleInternalHom C M]

/-- The composition morphism `Hom(n, p) ⊗ Hom(m, n) ⟶ Hom(m, p)` of internal Homs,
defined via the action associator and the evaluation morphisms. -/
def moduleIHomComp (m n p : M) :
    moduleIHom (C := C) n p ⊗ moduleIHom m n ⟶ moduleIHom m p :=
  moduleIHomEquiv _ m p
    ((actμ_ (moduleIHom n p) (moduleIHom m n) m).hom ≫
      (moduleIHom n p) ◁ᵐ moduleIHomEv m n ≫
      moduleIHomEv n p)

end CategoryTheory
