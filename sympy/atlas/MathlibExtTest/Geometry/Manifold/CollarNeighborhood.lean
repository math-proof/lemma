/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Geometry/Manifold/CollarNeighborhood.lean -/


import sympy.atlas.Geometry.Manifold.CollarNeighborhood
import Lemma.Set.Manifold.CollarNeighborhood

open Manifold Set
open scoped Manifold

open MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

-- The collar image is an open neighborhood of the manifold boundary.
example {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M] [T2Space M] [SecondCountableTopology M] :
    ∃ U : Set M, IsOpen U ∧ ModelWithCorners.boundary (I := 𝓡∂ n) M ⊆ U := by
  obtain ⟨c, hc, hzero⟩ :=
    topological_collar_neighborhood_of_smooth_manifold_with_boundary (n := n) (M := M)
  refine ⟨range c, hc.isOpen_range, ?_⟩
  intro x hx
  let b : ↥(ModelWithCorners.boundary (I := 𝓡∂ n) M) := ⟨x, hx⟩
  exact ⟨(b, ⟨0, by simp⟩), hzero b⟩
