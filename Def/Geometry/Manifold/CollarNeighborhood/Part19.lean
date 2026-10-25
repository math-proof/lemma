/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Theorem.Geometry.Manifold.CollarNeighborhood.Part19
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

def collarExtendedPositivePart
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    d.carrier × Set.Ioo (0 : ℝ) 1 → collarExternal X A :=
  collarExternalInteriorMap A ∘ collarLocalPositiveMap d

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
