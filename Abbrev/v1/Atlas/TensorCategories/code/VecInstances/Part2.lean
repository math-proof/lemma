/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecInstances.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Abbrev.v1.Atlas.TensorCategories.code.TensorCategoryDef.Part3
public import Theorem.Category.Atlas.v1.TensorCategories.code.TensorCategoryDef
public import Instance.v1.Atlas.TensorCategories.code.VecInstances.Part3
@[expose] public noncomputable section
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Limits

universe v u


namespace VecInstances

section FiniteLength

variable (k : Type u) [Field k]

/-- Convenient alias for Definition 1.12.3: the canonical isomorphism
`End(𝟙_ Vec_k) ≅ k`. -/
abbrev def_1_12_3_endUnit_iso (k : Type u) [Field k] :=
  endUnitAlgEquiv k

end FiniteLength
end VecInstances
end
