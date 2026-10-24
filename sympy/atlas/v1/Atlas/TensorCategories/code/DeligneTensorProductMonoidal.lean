/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DeligneTensorProductMonoidal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.DeligneTensorProduct
import Lemma.Category.Atlas.v1.TensorCategories.code.DeligneTensorProduct
import Lemma.Category.Atlas.v1.TensorCategories.code.TensorCategoryDef
import sympy.atlas.v1.Atlas.TensorCategories.code.TensorCategoryDef

set_option maxHeartbeats 400000

noncomputable section

open TensorProduct CategoryTheory

namespace Deligne

open TensorCategories

/-- Proposition 1.46.3: if `C` and `D` are multitensor categories, then the Deligne
tensor product `C ⊠ D` carries a natural multitensor category structure (with
compatible monoidal, preadditive, linear and rigid structures). -/
end Deligne

open Deligne TensorCategories CategoryTheory in
/-- Proposition 1.46.3 (root-namespace alias): if `C` and `D` are multitensor categories
then their Deligne tensor product `C ⊠ D` inherits a multitensor category structure. -/
end
