/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/HyperplaneChambers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic
import Def.v1.Atlas.Buildings.code.Reflection.HyperplaneChambers
open scoped InnerProductSpace
open Set


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineHyperplane

/-- The affine subspace associated to a hyperplane is nonempty (it contains the base
point). -/
instance instNonemptyToAffineSubspace [CompleteSpace E] (h : AffineHyperplane E) :
    Nonempty h.toAffineSubspace :=
  ⟨⟨h.basePoint, by
    change h.basePoint ∈ h.carrier
    simp only [basePoint, carrier, Set.mem_setOf_eq, inner_smul_right, real_inner_self_eq_norm_sq]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr h.normal_ne_zero))⟩⟩

end AffineHyperplane
end
