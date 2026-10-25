/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHomEssSurjInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.ExactModuleCatEquiv.Part3
import Class.v1.Atlas.TensorCategories.code.ConcreteModuleCategories.Part4
import Def.v1.Atlas.TensorCategories.code.InternalHomEssSurjInstance
set_option autoImplicit false

universe v u


namespace CategoryTheory

namespace InternalHomEssSurjInst

open Category MonoidalCategory MonObj LeftModCat

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- The `InternalHomData` for `C` acting on itself with generator `𝟙_ C`, endomorphism
algebra `𝟙_ C`, and functor `unitInternalHomFunctor'`. -/
noncomputable instance unitInternalHomData' :
    InternalHomData C C where
  gen := 𝟙_ C
  endAlgebra := ⟨𝟙_ C⟩
  F := unitInternalHomFunctor' C

end InternalHomEssSurjInst
end CategoryTheory
