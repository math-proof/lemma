/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part2
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/-- Every boundary point in an arbitrary atlas chart lies on its zero-coordinate face. -/
theorem collarBoundaryCoordZeroOfChart
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) {x : M} (hx : x ∈ e.source)
    (hxb : x ∈ ModelWithCorners.boundary (I := 𝓡∂ n) M) :
    (e x).val 0 = 0 := by
  change (𝓡∂ n).IsBoundaryPoint x at hxb
  have hfront : e.extend (𝓡∂ n) x ∈ frontier (e.extend (𝓡∂ n)).target :=
    ((𝓡∂ n).isBoundaryPoint_iff_of_mem_atlas (n := (⊤ : ℕ∞)) (by simp) he hx).mp hxb
  have htarget : e.extend (𝓡∂ n) x ∈ (e.extend (𝓡∂ n)).target :=
    (e.extend (𝓡∂ n)).map_source (by simpa [e.extend_source] using hx)
  have hnint : e.extend (𝓡∂ n) x ∉ interior (e.extend (𝓡∂ n)).target :=
    (mem_frontier_iff_notMem_interior htarget).mp hfront
  have hnint' : e.extend (𝓡∂ n) x ∉ interior (range (𝓡∂ n)) := by
    rwa [(e.extend_target_eventuallyEqSet (I := 𝓡∂ n) hx).mem_interior_iff] at hnint
  have hrange : e.extend (𝓡∂ n) x ∈ range (𝓡∂ n) :=
    e.extend_target_subset_range htarget
  have hfront' : e.extend (𝓡∂ n) x ∈ frontier (range (𝓡∂ n)) :=
    (mem_frontier_iff_notMem_interior hrange).mpr hnint'
  rw [frontier_range_modelWithCornersEuclideanHalfSpace, e.extend_coe] at hfront'
  simpa using hfront'.symm

/-- In any atlas chart, the boundary is exactly the zero-coordinate face. -/
theorem collarMemBoundaryIffCoordZeroOfChart
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace n)}
    (he : e ∈ atlas (EuclideanHalfSpace n) M) {x : M} (hx : x ∈ e.source) :
    x ∈ ModelWithCorners.boundary (I := 𝓡∂ n) M ↔ (e x).val 0 = 0 := by
  constructor
  · exact collarBoundaryCoordZeroOfChart he hx
  · intro hz
    apply ((𝓡∂ n).isBoundaryPoint_iff_of_mem_atlas
      (n := (⊤ : ℕ∞)) (by simp) he hx).mpr
    have htarget : e.extend (𝓡∂ n) x ∈ (e.extend (𝓡∂ n)).target :=
      (e.extend (𝓡∂ n)).map_source (by simpa [e.extend_source] using hx)
    have hrange : e.extend (𝓡∂ n) x ∈ range (𝓡∂ n) :=
      e.extend_target_subset_range htarget
    have hfront : e.extend (𝓡∂ n) x ∈ frontier (range (𝓡∂ n)) := by
      rw [frontier_range_modelWithCornersEuclideanHalfSpace, e.extend_coe]
      simpa using hz.symm
    have hnintRange : e.extend (𝓡∂ n) x ∉ interior (range (𝓡∂ n)) :=
      (mem_frontier_iff_notMem_interior hrange).mp hfront
    have hnintTarget :
        e.extend (𝓡∂ n) x ∉ interior (e.extend (𝓡∂ n)).target := by
      intro hint
      exact hnintRange
        ((e.extend_target_eventuallyEqSet (I := 𝓡∂ n) hx).mem_interior_iff.mp hint)
    exact (mem_frontier_iff_notMem_interior htarget).mpr hnintTarget

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
