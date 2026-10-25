/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/ThreeManifold.lean -/

import Mathlib.Geometry.Manifold.Instances.Real


/-!
# Topological 3-manifolds

A **topological 3-manifold** is a topological space that is locally homeomorphic to `ℝ³`,
Hausdorff, and second-countable.  In Mathlib, "locally homeomorphic to `ℝ³`" is exactly a
`ChartedSpace (EuclideanSpace ℝ (Fin 3)) M` instance, so `IsThreeManifold` is a thin predicate
over the `ChartedSpace` API bundling the two remaining point-set conditions.

We also provide the manifold-with-boundary variant `IsThreeManifoldWithBoundary`, modelled on the
Euclidean half-space `EuclideanHalfSpace 2`.

## Main definitions

* `IsThreeManifold M`: `M` is a (boundaryless) topological 3-manifold.
* `IsThreeManifoldWithBoundary M`: `M` is a topological 3-manifold with boundary.

## References

* John M. Lee, *Introduction to Topological Manifolds*, definition of a topological manifold.
-/

/-- A **topological 3-manifold**: a Hausdorff, second-countable topological space that is locally
homeomorphic to `ℝ³` (encoded by a `ChartedSpace (EuclideanSpace ℝ (Fin 3)) M` instance). -/
class IsThreeManifold (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] : Prop
    extends T2Space M, SecondCountableTopology M

/-- A **topological 3-manifold with boundary**: a Hausdorff, second-countable topological space
locally homeomorphic to the Euclidean half-space `EuclideanHalfSpace 2`. -/
class IsThreeManifoldWithBoundary (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M] : Prop
    extends T2Space M, SecondCountableTopology M

