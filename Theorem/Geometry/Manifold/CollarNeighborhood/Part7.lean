/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part7
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarExternalInteriorMap_continuous
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Continuous (collarExternalInteriorMap A) := by
  exact collarExternalBase_continuous.comp continuous_subtype_val

theorem collarExternalInteriorMap_isEmbedding
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.IsEmbedding (collarExternalInteriorMap A) := by
  apply Topology.IsEmbedding.of_comp collarExternalInteriorMap_continuous continuous_subtype_val
  change Topology.IsEmbedding (fun x : ↥(Aᶜ) ↦ (x.val, (0 : ℝ)))
  exact (isEmbedding_prodMkLeft 0).comp Topology.IsEmbedding.subtypeVal

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
