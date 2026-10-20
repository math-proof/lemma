import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Manifold.CollarNeighborhood
open Filter Function Manifold Set WithLp
open scoped ContDiff Manifold Topology
open MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted


/--
[topological_collar_neighborhood_of_smooth_manifold_with_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma topological_collar_neighborhood_of_smooth_manifold_with_boundary_eq
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M] :
-- imply
  ∃ (c : (↥(ModelWithCorners.boundary (I := by
-- proof
  apply MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted.topological_collar_neighborhood_of_smooth_manifold_with_boundary


-- created on 2026-10-20
