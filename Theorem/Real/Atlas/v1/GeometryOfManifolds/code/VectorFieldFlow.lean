module

public import Mathlib
public import Structure.v1.Atlas.GeometryOfManifolds.code.VectorFieldFlow

public section

open Manifold Topology Metric Set


/--
[SmoothFlow.toFun_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/VectorFieldFlow.lean)
-/
public theorem SmoothFlow.toFun_zero
  {n : ℕ}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ⊤ M]
  {φ : SmoothFlow n M}
  {x : M} :
-- imply
  φ.toFun 0 x = x :=
-- proof
  φ.map_zero x


-- created on 2026-10-23
