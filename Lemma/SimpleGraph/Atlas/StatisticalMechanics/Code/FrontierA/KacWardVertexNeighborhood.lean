import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardVertexNeighborhood
open StatMech StatMech.FrontierA


/--
[KWFiniteSimplePolygon.exists_vertexNeighborhoodData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVertexNeighborhood.lean)
-/
@[path]
private lemma exists_vertexNeighborhoodData_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n} :
-- imply
  Nonempty (KWVertexNeighborhoodData polygon) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_vertexNeighborhoodData polygon

/--
[KWVertexNeighborhoodData.vertexBall_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVertexNeighborhood.lean)
-/
@[path]
private lemma vertexBall_disjoint_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {data : KWVertexNeighborhoodData polygon}
  {i j : Fin n}
-- given
  (hij : i ≠ j) :
-- imply
  Disjoint (data.vertexBall i) (data.vertexBall j) := by
-- proof
  apply StatMech.FrontierA.KWVertexNeighborhoodData.vertexBall_disjoint data hij

/--
[KWVertexNeighborhoodData.vertexBall_disjoint_edgeTube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVertexNeighborhood.lean)
-/
@[path]
private lemma vertexBall_disjoint_edgeTube_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {data : KWVertexNeighborhoodData polygon}
  {v j : Fin n}
-- given
  (hvj : KWVertexEdgeNonincident v j) :
-- imply
  Disjoint (data.vertexBall v) (data.edgeTube j) := by
-- proof
  apply StatMech.FrontierA.KWVertexNeighborhoodData.vertexBall_disjoint_edgeTube data hvj


-- created on 2026-10-23
