/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/SimpleGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.AlgebraNotes.code.SimpleGroups.Part2


namespace SimpleGroups

open Matrix

section OneParamSubgroupTheorem

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable def diagRotationToLongI (θ : ℝ) : longitudeI :=
  ⟨⟨diagRotation θ, diagRotation_mem_SU2 θ⟩, ⟨θ, rfl⟩⟩

end OneParamSubgroupTheorem
end SimpleGroups
