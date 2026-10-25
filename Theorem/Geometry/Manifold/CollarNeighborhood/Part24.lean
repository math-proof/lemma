/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part23
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarPartialWeight_zero
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (a : A) : collarPartialWeight g 0 a = 0 := by
  simp [collarPartialWeight]

theorem collarPartialWeight_succ
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) (a : A) :
    collarPartialWeight g (m + 1) a = collarPartialWeight g m a + g.weight m a := by
  simp [collarPartialWeight, Finset.sum_range_succ]

theorem collarPartialWeight_eventually_eq_one
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (a : A) :
    ∃ m, collarPartialWeight g m =ᶠ[nhds a] 1 := by
  obtain ⟨I, hI⟩ := g.weight.exists_finset_nhds a
  obtain ⟨m, hIm⟩ := I.exists_nat_subset_range
  refine ⟨m, hI.mono ?_⟩
  intro b hb
  have hsupp : support (g.weight · b) ⊆ Finset.range m := hb.2.trans hIm
  calc
    collarPartialWeight g m b = ∑ᶠ k, g.weight k b :=
      (finsum_eq_sum_of_support_subset _ hsupp).symm
    _ = 1 := g.weight.sum_eq_one (mem_univ b)

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
