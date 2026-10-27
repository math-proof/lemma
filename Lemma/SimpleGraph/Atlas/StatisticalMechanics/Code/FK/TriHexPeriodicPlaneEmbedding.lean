import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.FK.TriHexPeriodicPlaneEmbedding.Part2
open Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triangularStraightEdgeArc_disjoint_of_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma triangularStraightEdgeArc_disjoint_of_intersection_eq
  {x y z w : Site 2}
-- given
  (hinter : TriangularStraightEdgeIntersectionProperty)
  (hxy : triangularGraph.Adj x y)
  (hzw : triangularGraph.Adj z w)
  (hxz : Ne x z)
  (hxw : Ne x w)
  (hyz : Ne y z)
  (hyw : Ne y w) :
-- imply
  Disjoint (Set.range (triangularStraightEdgeArc hxy)) (Set.range (triangularStraightEdgeArc hzw)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularStraightEdgeArc_disjoint_of_intersection hinter hxy hzw hxz hxw hyz hyw

/--
[hexagonalStraightEdgeArc_disjoint_of_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma hexagonalStraightEdgeArc_disjoint_of_intersection_eq
  {x y z w : HexVertex}
-- given
  (hinter : HexagonalStraightEdgeIntersectionProperty)
  (hxy : hexagonalGraph.Adj x y)
  (hzw : hexagonalGraph.Adj z w)
  (hxz : Ne x z)
  (hxw : Ne x w)
  (hyz : Ne y z)
  (hyw : Ne y w) :
-- imply
  Disjoint (Set.range (hexagonalStraightEdgeArc hxy)) (Set.range (hexagonalStraightEdgeArc hzw)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalStraightEdgeArc_disjoint_of_intersection hinter hxy hzw hxz hxw hyz hyw


-- created on 2026-10-23
