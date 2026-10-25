/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Theorem.Geometry.Manifold.CollarNeighborhood.Part38
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

def collarShiftHomeomorph : Set.Ico (0 : ℝ) 1 ≃ₜ Set.Ico (-1 : ℝ) 0 where
  toFun t := ⟨t.val - 1, by linarith [t.property.1], by linarith [t.property.2]⟩
  invFun s := ⟨s.val + 1, by linarith [s.property.1], by linarith [s.property.2]⟩
  left_inv t := by
    apply Subtype.ext
    ring
  right_inv s := by
    apply Subtype.ext
    ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def collarShiftInclusion : Set.Ico (-1 : ℝ) 0 → Set.Ico (-2 : ℝ) 0 :=
  Set.inclusion fun _ hs ↦ ⟨hs.1.trans' (by norm_num), hs.2⟩

def collarStripMap
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    A × Set.Ico (0 : ℝ) 1 → collarExternal X A :=
  collarExternalNegativeMap A ∘
    Prod.map id (collarShiftInclusion ∘ collarShiftHomeomorph)

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
