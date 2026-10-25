/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part33
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarStripMap_val
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (z : A × Set.Ico (0 : ℝ) 1) :
    (collarStripMap A z).val = (z.1.val, z.2.val - 1) := by
  rfl

theorem collarStripMap_mem_stage
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) (z : A × Set.Ico (0 : ℝ) 1)
    (hm : collarPartialWeight g m z.1 = 1) : collarStripMap A z ∈ collarStage g m := by
  right
  rw [collarStripMap_val]
  refine ⟨z.1.property, ?_⟩
  have ha : (⟨z.1.val, z.1.property⟩ : A) = z.1 := by
    apply Subtype.ext
    rfl
  rw [ha, hm]
  linarith [z.2.property.1]

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
