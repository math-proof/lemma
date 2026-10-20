import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Manifold.TubularNeighborhood
open Manifold Topology Filter Metric
open scoped Manifold ContDiff
open Topology
open scoped ContDiff
open Manifold Topology
open MathlibExt.Geometry.Manifold.TubularNeighborhoodWanted


/--
[tubular_smoothRetraction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/TubularNeighborhood.lean)
-/
@[path]
private lemma tubular_smoothRetraction_eq
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SecondCountableTopology M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I (⊤ : ℕ∞) M]
  {n : ℕ}
  {e : M → EuclideanSpace ℝ (Fin n)}
-- given
  (he : IsSmoothEmbedding I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) e)
  (hclosed : IsClosed (Set.range e)) :
-- imply
  ∃ (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
    (hU_sup : Set.range e ⊆ (U : Set (EuclideanSpace ℝ (Fin n)))),
    ∃ (r : ↥U → M),
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) I (⊤ : ℕ∞) r ∧
    ∀ (x : M), r ⟨e x, hU_sup ⟨x, rfl⟩⟩ = x := by
-- proof
  apply MathlibExt.Geometry.Manifold.TubularNeighborhoodWanted.tubular_smoothRetraction e he hclosed


-- created on 2026-10-20
