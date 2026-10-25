/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part5
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarExternal_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    IsClosed ((Set.univ ×ˢ ({0} : Set ℝ)) ∪ (A ×ˢ Set.Icc (-2 : ℝ) 0)) := by
  exact (isClosed_univ.prod isClosed_singleton).union (hA.prod isClosed_Icc)

theorem collarExternalBase_isClosedEmbedding
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.IsClosedEmbedding (collarExternalBase A) := by
  have hprod : Topology.IsClosedEmbedding (fun x : X ↦ (x, (0 : ℝ))) := by
    refine ⟨isEmbedding_prodMkLeft 0, ?_⟩
    convert (isClosed_univ.prod (isClosed_singleton : IsClosed ({0} : Set ℝ))) using 1
    ext p
    rcases p with ⟨x, t⟩
    simp [eq_comm]
  apply Topology.IsClosedEmbedding.of_comp
    (collarExternal_isClosed hA).isClosedEmbedding_subtypeVal.isEmbedding
  simpa [Function.comp_def, collarExternalBase] using hprod

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
