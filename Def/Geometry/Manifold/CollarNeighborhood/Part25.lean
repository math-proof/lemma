/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Theorem.Geometry.Manifold.CollarNeighborhood.Part25
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

def collarChartPush
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) :
    (g.data k).carrier × Set.Ico (-2 : ℝ) 1 →
      (g.data k).carrier × Set.Ico (-2 : ℝ) 1 :=
  fun z ↦ (z.1, collarFiberTransform (collarChartPushParameters g k z.1, z.2))

def collarChartPushInv
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) :
    (g.data k).carrier × Set.Ico (-2 : ℝ) 1 →
      (g.data k).carrier × Set.Ico (-2 : ℝ) 1 :=
  fun z ↦ (z.1, collarFiberTransform
    (((collarChartPushParameters g k z.1).2, (collarChartPushParameters g k z.1).1), z.2))

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
