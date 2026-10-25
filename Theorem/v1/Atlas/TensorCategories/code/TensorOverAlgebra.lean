/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorOverAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.AlgebrasInCategories.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.AlgebrasInCategories
universe v u

/-- Definition 2.9.22: the tensor product `M ⊗_A N` of a right `A`-module `M` and a left
`A`-module `N` in a monoidal category, constructed as a coequalizer. -/


section TensorOverAlgebra

variable {A : C} [MonObj A] [HasCoequalizers C]

end TensorOverAlgebra

namespace CategoryTheory

open Category MonoidalCategory Limits MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

end CategoryTheory
