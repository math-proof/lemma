/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/SemidirectProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Reflection.AffineWeylGroups

open scoped InnerProductSpace
open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineReflectionGroup

variable (W : AffineReflectionGroup E)

/-- The **stabilizer subgroup** $W_x = \{g \in W : g \cdot x = x\}$ of a point $x \in E$. -/
def Stabilizer (x : E) : Subgroup (E ≃ᵃⁱ[ℝ] E) where
  carrier := {g ∈ W.group | g x = x}
  mul_mem' := by
    intro a b ⟨ha_W, ha_fix⟩ ⟨hb_W, hb_fix⟩
    exact ⟨W.group.mul_mem ha_W hb_W, by change a (b x) = x; rw [hb_fix, ha_fix]⟩
  one_mem' := ⟨W.group.one_mem, rfl⟩
  inv_mem' := by
    intro a ⟨ha_W, ha_fix⟩
    refine ⟨W.group.inv_mem ha_W, ?_⟩
    show a⁻¹ x = x
    calc a⁻¹ x = a⁻¹ (a x) := by rw [ha_fix]
      _ = (a⁻¹ * a) x := rfl
      _ = (1 : E ≃ᵃⁱ[ℝ] E) x := by rw [inv_mul_cancel]
      _ = x := rfl

end AffineReflectionGroup
