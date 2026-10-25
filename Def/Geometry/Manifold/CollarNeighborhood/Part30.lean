/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Theorem.Geometry.Manifold.CollarNeighborhood.Part34
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

def collarExtendedChartHomeomorph
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A)
    (d : collarLocalData X A) :
    d.carrier × Set.Ico (-2 : ℝ) 1 ≃ₜ range (collarExtendedChart d) :=
  (collarExtendedChart_isOpenEmbedding hA d).isEmbedding.toHomeomorph

def collarRangePushHomeomorph
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (k : ℕ) :
    collarChartRange g k ≃ₜ collarChartRange g k :=
  (collarExtendedChartHomeomorph hA (g.data k)).symm.trans
    ((collarChartPushHomeomorph g k).trans
      (collarExtendedChartHomeomorph hA (g.data k)))

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
