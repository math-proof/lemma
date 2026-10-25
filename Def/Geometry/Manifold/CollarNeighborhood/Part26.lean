/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Theorem.Geometry.Manifold.CollarNeighborhood.Part26
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

def collarChartPushHomeomorph
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (k : ℕ) :
    (g.data k).carrier × Set.Ico (-2 : ℝ) 1 ≃ₜ
      (g.data k).carrier × Set.Ico (-2 : ℝ) 1 where
  toFun := collarChartPush g k
  invFun := collarChartPushInv g k
  left_inv := collarChartPush_leftInverse g k
  right_inv := collarChartPush_rightInverse g k
  continuous_toFun := collarChartPush_continuous g k
  continuous_invFun := collarChartPushInv_continuous g k

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
