/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Abbrev.Geometry.Manifold.CollarNeighborhood.Part11
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarChartSupport_isCompact
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) : IsCompact (collarChartSupport g k) := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  have hrange : tsupport (g.weight k) ⊆
      range (Subtype.val : (g.data k).carrier → A) := by
    intro a ha
    exact ⟨⟨a, g.subordinate k ha⟩, rfl⟩
  rw [image_preimage_eq_inter_range, inter_eq_left.mpr hrange]
  exact g.compact_tsupport k

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
