/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InternalHomEssSurjInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.ExactModuleCatEquiv.Part3
import Class.v1.Atlas.TensorCategories.code.ConcreteModuleCategories.Part4
import Def.v1.Atlas.TensorCategories.code.InternalHomEssSurjInstance.Part2
set_option autoImplicit false

universe v u


namespace CategoryTheory

namespace InternalHomEssSurjInst

open Category MonoidalCategory MonObj LeftModCat

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- Essential surjectivity of the unit internal Hom functor: every right `𝟙_ C`-module is
isomorphic to one in the image of `unitInternalHomFunctor'`. -/
noncomputable instance unitInternalHomEssSurj' :
    InternalHomEssSurj C C where
  essSurj := Functor.EssSurj.mk (fun L =>
    ⟨L.X, ⟨rightModUnitIso' C L⟩⟩)

end InternalHomEssSurjInst
end CategoryTheory
