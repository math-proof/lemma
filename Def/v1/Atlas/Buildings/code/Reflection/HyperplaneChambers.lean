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
import Structure.v1.Atlas.Buildings.code.Reflection.HyperplaneChambers
open scoped InnerProductSpace
open Set


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineHyperplane

/-- The underlying set $\{x : ⟨n, x⟩ = c\}$ of the affine hyperplane. -/
def carrier (h : AffineHyperplane E) : Set E :=
  {x : E | ⟪h.normal, x⟫_ℝ = h.offset}

/-- The open positive half-space $\{x : ⟨n, x⟩ > c\}$. -/
def positiveHalfSpace (h : AffineHyperplane E) : Set E :=
  {x : E | ⟪h.normal, x⟫_ℝ > h.offset}

/-- The open negative half-space $\{x : ⟨n, x⟩ < c\}$. -/
def negativeHalfSpace (h : AffineHyperplane E) : Set E :=
  {x : E | ⟪h.normal, x⟫_ℝ < h.offset}

/-- The hyperplane $h$ *separates* $x$ and $y$ if they lie in opposite open half-spaces. -/
def Separates (h : AffineHyperplane E) (x y : E) : Prop :=
  (⟪h.normal, x⟫_ℝ > h.offset ∧ ⟪h.normal, y⟫_ℝ < h.offset) ∨
  (⟪h.normal, x⟫_ℝ < h.offset ∧ ⟪h.normal, y⟫_ℝ > h.offset)

/-- $η$ is a *wall* of $C$ if some open neighborhood of a point of $η$ meets $η$ inside the
closure of $C$. -/
def IsWall (η : AffineHyperplane E) (C : Set E) : Prop :=
  ∃ U : Set E, IsOpen U ∧ (U ∩ η.carrier).Nonempty ∧ U ∩ η.carrier ⊆ closure C

/-- A canonical base point of $η$: the orthogonal projection of $0$ onto $η$. -/
def basePoint (h : AffineHyperplane E) : E :=
  (h.offset / ⟪h.normal, h.normal⟫_ℝ) • h.normal

/-- The direction subspace (parallel translate to the origin) of $η$, equal to $n^⊥$. -/
def direction (h : AffineHyperplane E) : Submodule ℝ E :=
  (Submodule.span ℝ {h.normal})ᗮ

/-- The affine hyperplane viewed as a Mathlib `AffineSubspace`. -/
def toAffineSubspace [CompleteSpace E] (h : AffineHyperplane E) : AffineSubspace ℝ E :=
  { carrier := h.carrier
    smul_vsub_vadd_mem' := by
      intro c x y z hx hy hz
      simp only [carrier, Set.mem_setOf_eq] at *
      simp only [vadd_eq_add, vsub_eq_sub,
        inner_add_right, inner_sub_right, inner_smul_right]
      rw [hx, hy, hz]; ring }

end AffineHyperplane
end
