/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorOverAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.AlgebrasInCategories
import Lemma.Category.Atlas.v1.TensorCategories.code.AlgebrasInCategories

universe v u

namespace CategoryTheory

open Category MonoidalCategory Limits MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section TensorOverAlgebra

variable {A : C} [MonObj A] [HasCoequalizers C]

/-- Definition 2.9.22: the tensor product `M ⊗_A N` of a right `A`-module `M` and a left
`A`-module `N` in a monoidal category, constructed as a coequalizer. -/
end TensorOverAlgebra

end CategoryTheory
