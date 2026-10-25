/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Theorem.Geometry.Manifold.CollarNeighborhood.Part43
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

def collarStageHomeomorph
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (m : ℕ) : X ≃ₜ collarStage g m :=
  (collarExternalBase_isClosedEmbedding hA).isEmbedding.toHomeomorph |>.trans
    ((Homeomorph.image (collarPartialPush hA g m) (range (collarExternalBase A))).trans
      (Homeomorph.setCongr (collarPartialPush_image_base hA g m)))

def collarStageStrip
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) (W : Set A)
    (hm : ∀ a ∈ W, collarPartialWeight g m a = 1) :
    W × Set.Ico (0 : ℝ) 1 → collarStage g m :=
  fun z ↦ ⟨collarStripMap A (z.1.val, z.2),
    collarStripMap_mem_stage g m (z.1.val, z.2) (hm z.1.val z.1.property)⟩

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
