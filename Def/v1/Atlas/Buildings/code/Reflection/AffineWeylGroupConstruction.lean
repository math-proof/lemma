/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroupConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.Reflection.AffineWeylGroups.Part3
import Structure.v1.Atlas.Buildings.code.Reflection.AffineWeylGroupConstruction
open scoped InnerProductSpace
open Set


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineWeylGroupFullData

variable (d : AffineWeylGroupFullData E)

/-- Shorthand for the underlying affine hyperplane arrangement of the affine Weyl data. -/
def affineArr : HyperplaneArrangement E :=
  d.toAffineWeylGroupData.affineArrangement

/-- Formula for the affine reflection across $H_{α,k}$:
$s_{α,k}(v) = v - (⟨α,v⟩ - k) \check α$. -/
def affineReflFun (α : E) (k : ℤ) (v : E) : E :=
  v - (⟪α, v⟫_ℝ - ↑k) • d.coroot α

/-- Formula for the linear reflection through the hyperplane perpendicular to $α$:
$s_α(v) = v - ⟨α,v⟩ \check α$. -/
def linearReflFun (α : E) (v : E) : E :=
  v - ⟪α, v⟫_ℝ • d.coroot α

end AffineWeylGroupFullData
end
