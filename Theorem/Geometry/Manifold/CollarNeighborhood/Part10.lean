/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part9
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarPositiveIntervalInclusion_isOpenEmbedding :
    Topology.IsOpenEmbedding collarPositiveIntervalInclusion := by
  refine Topology.IsOpenEmbedding.inclusion
    (show Set.Ioo (0 : ℝ) 1 ⊆ Set.Ico (0 : ℝ) 1 from fun _ hx ↦ ⟨hx.1.le, hx.2⟩) ?_
  have h : (Subtype.val : Set.Ico (0 : ℝ) 1 → ℝ) ⁻¹' Set.Ioo (0 : ℝ) 1 =
      {x | 0 < x.val} := by
    ext x
    exact and_iff_left x.property.2
  rw [h]
  exact isOpen_lt continuous_const continuous_subtype_val

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
