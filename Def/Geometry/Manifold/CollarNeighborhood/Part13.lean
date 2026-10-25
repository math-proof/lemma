/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Theorem.Geometry.Manifold.CollarNeighborhood.Part13
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

def collarExtendedChart
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    d.carrier × Set.Ico (-2 : ℝ) 1 → collarExternal X A :=
  fun z ↦ if hz : z.2.val ≤ 0 then
    ⟨(z.1.val.val, z.2.val), Or.inr ⟨z.1.val.property, z.2.property.1, hz⟩⟩
  else
    collarExternalBase A
      (d.map (z.1, ⟨z.2.val, (le_of_lt (lt_of_not_ge hz)), z.2.property.2⟩))

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
