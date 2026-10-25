/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/ThreeManifold.lean -/

import Mathlib.Geometry.Manifold.Instances.Real
import Class.Topology.ThreeManifold
variable (M : Type*) [TopologicalSpace M]


/-- Every topological 3-manifold with boundary is Hausdorff. -/
example [ChartedSpace (EuclideanHalfSpace 2) M] [IsThreeManifoldWithBoundary M] : T2Space M :=
  inferInstance

/-- `ℝ³` is a topological 3-manifold (the model, boundaryless case). -/
example : IsThreeManifold (EuclideanSpace ℝ (Fin 3)) := ⟨⟩

/-- The Euclidean half-space is a topological 3-manifold with boundary (boundary case). -/
example : IsThreeManifoldWithBoundary (EuclideanHalfSpace 2) :=
  haveI : SecondCountableTopology (EuclideanHalfSpace 2) :=
    Topology.IsEmbedding.subtypeVal.isInducing.secondCountableTopology
  haveI : T2Space (EuclideanHalfSpace 2) := Topology.IsEmbedding.subtypeVal.t2Space
  ⟨⟩

