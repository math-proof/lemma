/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarModelMap_zero (n : ℕ) [NeZero n] {r : ℝ} (hr : 0 < r)
    (x : collarFace n) :
    collarModelMap n r (x, ⟨0, by exact ⟨le_rfl, hr⟩⟩) = x.val := by
  apply EuclideanHalfSpace.ext
  apply PiLp.ext
  intro i
  by_cases hi : i = 0
  · subst i
    simpa [collarModelMap, collarIcoToIci, collarHalfSpaceSplit] using x.property.symm
  · simp [collarModelMap, collarIcoToIci, collarHalfSpaceSplit, hi]

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
