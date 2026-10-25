/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Reflection.HyperplaneChambers.Part4
import Theorem.v1.Atlas.Buildings.code.Reflection.WallSeparationCorollary
import Structure.v1.Atlas.Buildings.code.Reflection.AffineWeylGroups.Part2
set_option maxHeartbeats 800000

open scoped InnerProductSpace
open Set

set_option maxHeartbeats 800000


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineWeylGroupData

variable (d : AffineWeylGroupData E)

/-- The affine hyperplane arrangement $\{H_{α,k} : α ∈ Φ,\ k ∈ ℤ\}$ associated to the
root system data. -/
def affineArrangement : HyperplaneArrangement E where
  hyperplanes := { η | ∃ α ∈ d.roots, ∃ k : ℤ, η.normal = α ∧ η.offset = ↑k }

end AffineWeylGroupData

namespace AffineReflectionGroup

variable (W : AffineReflectionGroup E)

/-- The pointwise stabilizer of $p ∈ E$ inside $W$. -/
def PointStabilizer (p : E) : Subgroup (E ≃ᵃⁱ[ℝ] E) where
  carrier := {g | g ∈ W.group ∧ g p = p}
  mul_mem' := by
    intro a b ⟨haW, hap⟩ ⟨hbW, hbp⟩
    refine ⟨W.group.mul_mem haW hbW, ?_⟩
    show (a * b) p = p
    simp only [AffineIsometryEquiv.coe_mul, Function.comp_apply, hbp, hap]
  one_mem' := ⟨W.group.one_mem, rfl⟩
  inv_mem' := by
    intro a ⟨haW, hap⟩
    refine ⟨W.group.inv_mem haW, ?_⟩
    have h := a.symm_apply_apply p
    rw [hap] at h
    exact h

end AffineReflectionGroup
end
