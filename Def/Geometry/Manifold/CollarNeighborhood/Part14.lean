/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Theorem.Geometry.Manifold.CollarNeighborhood.Part14
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

def collarExtendedNegative
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    d.carrier × Set.Ico (-2 : ℝ) 1 → collarExternal X A :=
  fun z ↦ ⟨(z.1.val.val, min z.2.val 0), Or.inr ⟨z.1.val.property,
    le_min z.2.property.1 (by norm_num), min_le_right _ _⟩⟩

def collarExtendedPositive
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    d.carrier × Set.Ico (-2 : ℝ) 1 → collarExternal X A :=
  fun z ↦ collarExternalBase A
    (d.map (z.1, ⟨max 0 z.2.val, le_max_left _ _, max_lt (by norm_num) z.2.property.2⟩))

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
