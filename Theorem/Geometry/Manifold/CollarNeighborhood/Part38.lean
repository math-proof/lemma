/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part32
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarPartialPush_image_base
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (m : ℕ) :
    collarPartialPush hA g m '' range (collarExternalBase A) = collarStage g m := by
  induction m with
  | zero =>
      simpa [collarPartialPush] using (collarStage_zero g).symm
  | succ k ih =>
      rw [show collarPartialPush hA g (k + 1) '' range (collarExternalBase A) =
          collarGlobalPush hA g k ''
            (collarPartialPush hA g k '' range (collarExternalBase A)) by
        rw [image_image]
        rfl]
      rw [ih, collarGlobalPush_image_stage hA g k]

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
