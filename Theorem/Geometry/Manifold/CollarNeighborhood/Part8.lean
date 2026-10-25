/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Abbrev.Geometry.Manifold.CollarNeighborhood.Part7
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarExternalInterior_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    IsOpen (collarExternalInterior X A) := by
  exact hA.isOpen_compl.preimage (continuous_fst.comp continuous_subtype_val)

theorem collarExternalInteriorMap_range
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    range (collarExternalInteriorMap A) = collarExternalInterior X A := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact x.property
  · intro hy
    rcases y.property with hy0 | hyA
    · refine ⟨⟨y.val.1, hy⟩, ?_⟩
      apply Subtype.ext
      change (y.val.1, (0 : ℝ)) = y.val
      apply Prod.ext
      · rfl
      · exact hy0.2.symm
    · exact (hy hyA.1).elim

theorem collarExternalInteriorMap_isOpenEmbedding
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    Topology.IsOpenEmbedding (collarExternalInteriorMap A) := by
  refine ⟨collarExternalInteriorMap_isEmbedding (X := X) (A := A), ?_⟩
  rw [collarExternalInteriorMap_range (X := X) (A := A)]
  exact collarExternalInterior_isOpen hA

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
