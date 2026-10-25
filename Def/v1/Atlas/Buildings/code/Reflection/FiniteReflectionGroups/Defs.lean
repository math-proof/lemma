/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/FiniteReflectionGroups/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Reflection.HyperplaneChambers.Part4
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Finite.Basic
open scoped InnerProductSpace
open Set


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace FiniteReflectionGroups

/-- Linear reflection across the hyperplane orthogonal to $α$:
$s_α(v) = v - (2⟨α,v⟩/⟨α,α⟩)·α$. -/
def linearReflection (α v : E) : E :=
  v - (2 * ⟪α, v⟫_ℝ / ⟪α, α⟫_ℝ) • α

/-- Linear reflection $s_α$ packaged as an $ℝ$-linear map. -/
def linearReflectionLM (α : E) : E →ₗ[ℝ] E where
  toFun v := v - (2 * ⟪α, v⟫_ℝ / ⟪α, α⟫_ℝ) • α
  map_add' x y := by
    simp only [inner_add_right, mul_add, add_div, add_smul]; abel
  map_smul' r x := by
    simp only [inner_smul_right, RingHom.id_apply]
    ring_nf; simp [smul_sub, smul_smul]; congr 1; ring

end FiniteReflectionGroups
end
