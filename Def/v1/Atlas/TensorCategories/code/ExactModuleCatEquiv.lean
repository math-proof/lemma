/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCatEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.AlgebrasInCategories.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.AlgebrasInCategories
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.InternalHom
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Def.v1.Atlas.TensorCategories.code.InternalHom.Part4
import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Structure.v1.Atlas.TensorCategories.code.ExactModuleCatEquiv
set_option maxHeartbeats 800000

set_option autoImplicit false

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory MonObj LeftModCat

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]


attribute [instance] InternalEndAlgebra.monObj

namespace InternalEndAlgebra

variable (A : InternalEndAlgebra (C := C))

/-- The multiplication morphism of the internal algebra. -/
noncomputable def mul : A.carrier ⊗ A.carrier ⟶ A.carrier := μ[A.carrier]

/-- The unit morphism of the internal algebra. -/
noncomputable def one : 𝟙_ C ⟶ A.carrier := η[A.carrier]

/-- Wrap an object `A : C` carrying a `MonObj` instance as an `InternalEndAlgebra`. -/
def ofMonObj (A : C) [MonObj A] : InternalEndAlgebra (C := C) where
  carrier := A

/-- The trivial internal algebra given by the monoidal unit `𝟙_ C`. -/
def ofUnit : InternalEndAlgebra (C := C) where
  carrier := 𝟙_ C

end InternalEndAlgebra
end CategoryTheory
