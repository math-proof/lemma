/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/SimpleGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.AlgebraNotes.code.SimpleGroups


namespace SimpleGroups

open Matrix

section OneParamSubgroupTheorem

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable def longitudeI : Subgroup SU2 where
  carrier := {M | ∃ θ : ℝ, M.val = diagRotation θ}
  mul_mem' := by
    intro a b ⟨θ₁, hθ₁⟩ ⟨θ₂, hθ₂⟩
    exact ⟨θ₁ + θ₂, by
      change (a * b).val = diagRotation (θ₁ + θ₂)
      change a.val * b.val = diagRotation (θ₁ + θ₂)
      rw [hθ₁, hθ₂, diagRotation_add]⟩
  one_mem' := ⟨0, by show (1 : SU2).val = diagRotation 0; simp [diagRotation_zero]⟩
  inv_mem' := by
    intro a ⟨θ, hθ⟩
    refine ⟨-θ, ?_⟩
    have hinv : a⁻¹ = ⟨diagRotation (-θ), diagRotation_mem_SU2 (-θ)⟩ := by
      have h : ⟨diagRotation (-θ), diagRotation_mem_SU2 (-θ)⟩ * a = 1 := by
        ext1
        show diagRotation (-θ) * a.val = 1
        rw [hθ, diagRotation_add]; simp [diagRotation_zero]
      exact (mul_eq_one_iff_eq_inv.mp h).symm
    show a⁻¹.val = diagRotation (-θ)
    rw [hinv]

end OneParamSubgroupTheorem
end SimpleGroups
