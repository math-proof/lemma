/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part17
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarExtendedNegativePart_isOpenEmbedding
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    Topology.IsOpenEmbedding (collarExtendedNegativePart d) := by
  exact collarExternalNegativeMap_isOpenEmbedding.comp
    (d.isOpen_carrier.isOpenEmbedding_subtypeVal.prodMap Topology.IsOpenEmbedding.id)

theorem collarExtendedChart_negative
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A)
    (z : d.carrier × Set.Ico (-2 : ℝ) 0) :
    collarExtendedChart d (z.1, collarNegativeIntervalInclusion z.2) =
      collarExtendedNegativePart d z := by
  apply Subtype.ext
  rw [collarExtendedChart_val_of_nonpos]
  · rfl
  · exact z.2.property.2.le

theorem collarExtendedChart_comp_negative
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A) :
    collarExtendedChart d ∘ collarExtendedNegativeInclusion d =
      collarExtendedNegativePart d := by
  funext z
  exact collarExtendedChart_negative d z

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
