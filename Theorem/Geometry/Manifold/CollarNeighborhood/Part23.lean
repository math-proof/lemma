/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part22
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarPartialWeight_continuous
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) : Continuous (collarPartialWeight g m) := by
  exact continuous_finsetSum _ fun k _ ↦ (g.weight k).continuous

theorem collarPartialWeight_nonneg
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) (a : A) : 0 ≤ collarPartialWeight g m a := by
  exact Finset.sum_nonneg fun k _ ↦ g.weight.nonneg k a

theorem collarPartialWeight_le_one
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) (a : A) : collarPartialWeight g m a ≤ 1 := by
  let I := Finset.range m ∪ g.weight.finsupport a
  have htotal : ∑ k ∈ I, g.weight k a = 1 :=
    g.weight.sum_finsupport' (mem_univ a) Finset.subset_union_right
  have hle : ∑ k ∈ Finset.range m, g.weight k a ≤ ∑ k ∈ I, g.weight k a := by
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    intro k hkI hk
    exact g.weight.nonneg k a
  rwa [htotal] at hle

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
