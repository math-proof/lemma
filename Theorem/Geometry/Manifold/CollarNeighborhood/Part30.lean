/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Abbrev.Geometry.Manifold.CollarNeighborhood.Part10
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarLowerHalf_isCompact : IsCompact collarLowerHalf := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  have himage : (Subtype.val : Set.Ico (-2 : ℝ) 1 → ℝ) '' collarLowerHalf =
      Set.Icc (-2 : ℝ) (1 / 2) := by
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t.property.1, ht⟩
    · intro hs
      let t : Set.Ico (-2 : ℝ) 1 := ⟨s, hs.1, hs.2.trans_lt (by norm_num)⟩
      exact ⟨t, hs.2, rfl⟩
  rw [himage]
  exact isCompact_Icc

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
