/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Structure.Geometry.Manifold.CollarNeighborhood
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

def collarLocalDataRestrict
    {X : Type*} [TopologicalSpace X] {A : Set X} (d : collarLocalData X A)
    (V : Set A) (hV : IsOpen V) (hVd : V ⊆ d.carrier) : collarLocalData X A := by
  let inc : V → d.carrier := Set.inclusion hVd
  have hinc : Topology.IsOpenEmbedding inc := by
    apply Topology.IsOpenEmbedding.inclusion hVd
    exact hV.preimage continuous_subtype_val
  let param : V × Set.Ico (0 : ℝ) 1 → d.carrier × Set.Ico (0 : ℝ) 1 :=
    Prod.map inc id
  exact
    { carrier := V
      isOpen_carrier := hV
      map := d.map ∘ param
      isOpenEmbedding_map := d.isOpenEmbedding_map.comp
        (hinc.prodMap Topology.IsOpenEmbedding.id)
      map_zero := fun u ↦ by
        change d.map (inc u, ⟨0, by simp⟩) = u.val.val
        simpa [inc] using d.map_zero (inc u)
      map_not_mem := fun z hz ↦ d.map_not_mem (param z) hz }

def collarScaleIco (d : ℝ) (hd₀ : 0 < d) (hd₁ : d ≤ 1) :
    Set.Ico (0 : ℝ) 1 → Set.Ico (0 : ℝ) 1 :=
  fun t ↦ ⟨d * t.val, mul_nonneg hd₀.le t.property.1,
    (mul_lt_mul_of_pos_left t.property.2 hd₀).trans_le (by simpa using hd₁)⟩

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
