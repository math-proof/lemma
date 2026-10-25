/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Theorem.Geometry.Manifold.CollarNeighborhood.Part42
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

def collarAnchor
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) (a : A) : collarExternal X A :=
  ⟨(a.val, -collarPartialWeight g m a), Or.inr ⟨a.property,
    by linarith [collarPartialWeight_le_one g m a],
    by linarith [collarPartialWeight_nonneg g m a]⟩⟩

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
