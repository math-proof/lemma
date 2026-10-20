import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Manifold.OneDimensional
open scoped Manifold ContDiff Topology Bundle
open scoped Manifold ContDiff
open MathlibExt.Geometry.Manifold.OneDimensionalClassification
open MathlibExt.Geometry.Manifold.OneDimensionalWanted


/--
[connected_boundaryless_one_manifold_classification](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma connected_boundaryless_one_manifold_classification_eq
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M] [T2Space M] [ConnectedSpace M] [SecondCountableTopology M] :
-- imply
  Nonempty (M ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle) ∨ Nonempty (M ≃ₘ⟮𝓡 1, 𝓡 1⟯ (EuclideanSpace ℝ (Fin 1))) := by
-- proof
  apply MathlibExt.Geometry.Manifold.OneDimensionalWanted.connected_boundaryless_one_manifold_classification M

/--
[compact_connected_one_manifold_with_boundary_classification](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean)
-/
@[path]
private lemma compact_connected_one_manifold_with_boundary_classification_eq
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M] :
-- imply
  Nonempty (M ≃ₘ⟮𝓡∂ 1, 𝓡 1⟯ Circle) ∨ Nonempty (M ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ (Set.Icc (0 : ℝ) 1)) := by
-- proof
  apply MathlibExt.Geometry.Manifold.OneDimensionalWanted.compact_connected_one_manifold_with_boundary_classification M


-- created on 2026-10-20
