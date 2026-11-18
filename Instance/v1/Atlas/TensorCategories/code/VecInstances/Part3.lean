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
public import Def.v1.Atlas.TensorCategories.code.VecInstances.Part2
public import Instance.v1.Atlas.TensorCategories.code.VecInstances.Part2
@[expose] public section
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Limits

universe v u


noncomputable section

namespace VecInstances

section FiniteLength

variable (k : Type u) [Field k]

/-- `Vec k` is a tensor category in the sense of Definition 1.12.3: a multitensor
category whose unit-endomorphism algebra is `k`. -/
instance tensorCategory_vec :
    TensorCategories.TensorCategory k (Vec k) where
  homFinite := fun _ _ => inferInstance
  hasFiniteLength := hasFiniteLength_vec k
  endUnit_iso_k := ⟨endUnitAlgEquiv k⟩

end FiniteLength
end VecInstances
end
