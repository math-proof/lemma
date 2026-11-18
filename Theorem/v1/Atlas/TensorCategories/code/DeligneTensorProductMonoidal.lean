/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DeligneTensorProductMonoidal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.TensorCategories.code.DeligneTensorProduct.Part3
public import Theorem.Category.Atlas.v1.TensorCategories.code.DeligneTensorProduct
public import Theorem.Category.Atlas.v1.TensorCategories.code.TensorCategoryDef
public import Abbrev.v1.Atlas.TensorCategories.code.TensorCategoryDef.Part3
set_option maxHeartbeats 400000

public section

/-! Proposition 1.46.3: if `C` and `D` are multitensor categories, then the Deligne
tensor product `C ⊠ D` carries a natural multitensor category structure (with
compatible monoidal, preadditive, linear and rigid structures). -/
/-! Proposition 1.46.3 (root-namespace alias): if `C` and `D` are multitensor categories
then their Deligne tensor product `C ⊠ D` inherits a multitensor category structure. -/


namespace Deligne

open TensorCategories

end Deligne

noncomputable section

open TensorProduct CategoryTheory

end
