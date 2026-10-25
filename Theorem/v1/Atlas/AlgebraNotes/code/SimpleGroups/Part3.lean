/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/SimpleGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.AlgebraNotes.code.SimpleGroups.Part4


namespace SimpleGroups

open Matrix

section OneParamSubgroupTheorem

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma diagRotationToLongI_periodic (a b : ℝ)
    (h : @Setoid.r _ (QuotientAddGroup.leftRel (AddSubgroup.zmultiples (2 * Real.pi))) a b) :
    diagRotationToLongI a = diagRotationToLongI b := by
  simp only [QuotientAddGroup.leftRel_apply] at h
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp h
  simp only [diagRotationToLongI]
  ext1; ext1
  show diagRotation a = diagRotation b
  have hba : b = a + n * (2 * Real.pi) := by
    have := hn; simp [zsmul_eq_mul] at this; linarith
  rw [hba, diagRotation_periodic]

end OneParamSubgroupTheorem
end SimpleGroups
