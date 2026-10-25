/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Theorem.Geometry.Manifold.CollarNeighborhood.Part12
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

def collarLocalDataScale
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A)
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1) : collarLocalData X A := by
  let param : d.carrier × Set.Ico (0 : ℝ) 1 → d.carrier × Set.Ico (0 : ℝ) 1 :=
    Prod.map id (collarScaleIco δ hδ₀ hδ₁)
  exact
    { carrier := d.carrier
      isOpen_carrier := d.isOpen_carrier
      map := d.map ∘ param
      isOpenEmbedding_map := d.isOpenEmbedding_map.comp
        (Topology.IsOpenEmbedding.id.prodMap
          (collarScaleIco_isOpenEmbedding δ hδ₀ hδ₁))
      map_zero := fun u ↦ by
        change d.map (u, collarScaleIco δ hδ₀ hδ₁ ⟨0, by simp⟩) = u.val.val
        simpa [collarScaleIco] using d.map_zero u
      map_not_mem := fun z hz ↦ by
        apply d.map_not_mem (param z)
        change 0 < δ * z.2.val
        exact mul_pos hδ₀ hz }

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
