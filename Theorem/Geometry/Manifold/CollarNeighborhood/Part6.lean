/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part6
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarExternalNegativeMap_range
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    range (collarExternalNegativeMap A) = collarExternalNegative X A := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact z.2.property.2
  · intro hy
    have ha : y.val.1 ∈ A := collarExternal_fst_mem_of_snd_lt y hy
    have hlow : -2 ≤ y.val.2 := by
      rcases y.property with hy0 | hyA
      · have hz : y.val.2 = 0 := hy0.2
        rw [hz]
        norm_num
      · exact hyA.2.1
    refine ⟨(⟨y.val.1, ha⟩, ⟨y.val.2, hlow, hy⟩), ?_⟩
    apply Subtype.ext
    rfl

theorem collarExternalNegativeMap_isOpenEmbedding
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.IsOpenEmbedding (collarExternalNegativeMap A) := by
  refine ⟨collarExternalNegativeMap_isEmbedding (X := X) (A := A), ?_⟩
  rw [collarExternalNegativeMap_range (X := X) (A := A)]
  exact collarExternalNegative_isOpen (X := X) (A := A)

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
