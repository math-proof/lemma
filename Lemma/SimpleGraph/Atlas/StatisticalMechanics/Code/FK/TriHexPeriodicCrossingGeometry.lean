import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
open Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triangularSegment_re_scaled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicCrossingGeometry.lean)
-/
@[path]
private lemma triangularSegment_re_scaled_eq
  {x y : Site 2}
  {t : unitInterval} :
-- imply
  3 * (Path.segment (triangularPlaneVertex x) (triangularPlaneVertex y) t).re = (t : Real) * ((3 * y 0 : Int) - (3 * x 0 : Int)) + (3 * x 0 : Int) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularSegment_re_scaled x y t

/--
[triangularSegment_im_scaled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicCrossingGeometry.lean)
-/
@[path]
private lemma triangularSegment_im_scaled_eq
  {x y : Site 2}
  {t : unitInterval} :
-- imply
  3 * (Path.segment (triangularPlaneVertex x) (triangularPlaneVertex y) t).im = (t : Real) * ((3 * y 1 : Int) - (3 * x 1 : Int)) + (3 * x 1 : Int) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularSegment_im_scaled x y t

/--
[triHexCanonicalPairedSegments_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicCrossingGeometry.lean)
-/
@[path]
private lemma triHexCanonicalPairedSegments_crossing_eq
  {a : TriHexEdgeIndex} :
-- imply
  ∃ t u : unitInterval, Path.segment (triangularPlaneVertex a.1) (triangularPlaneVertex (a.1 + triangularStep a.2)) t = Path.segment (hexagonalPlaneVertex ((triHexIndexEquiv a).1, false)) (hexagonalPlaneVertex ((triHexIndexEquiv a).1 + hexagonalStep (triHexIndexEquiv a).2, true)) u := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexCanonicalPairedSegments_crossing a

/--
[triHexCanonicalSegments_of_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicCrossingGeometry.lean)
-/
@[path]
private lemma triHexCanonicalSegments_of_crossing_eq
  {x z : Site 2}
  {i j : Fin 3}
  {p : Complex}
-- given
  (hp : p ∈ Set.range (Path.segment (triangularPlaneVertex x) (triangularPlaneVertex (x + triangularStep i))))
  (hq : p ∈ Set.range (Path.segment (hexagonalPlaneVertex (z, false)) (hexagonalPlaneVertex (z + hexagonalStep j, true)))) :
-- imply
  triHexIndexEquiv (x, i) = (z, j) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexCanonicalSegments_of_crossing x z i j p hp hq

/--
[triangularStraightEdgeArc_range_chart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicCrossingGeometry.lean)
-/
@[path]
private lemma triangularStraightEdgeArc_range_chart_eq
  {x y : Site 2}
-- given
  (hxy : triangularGraph.Adj x y) :
-- imply
  let e : triangularGraph.edgeSet := ⟨s(x, y), hxy⟩ let a := triangularEdgeChartEquiv.symm e Set.range (triangularStraightEdgeArc hxy) = Set.range (Path.segment (triangularPlaneVertex a.1) (triangularPlaneVertex (a.1 + triangularStep a.2))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularStraightEdgeArc_range_chart hxy

/--
[hexagonalStraightEdgeArc_range_chart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicCrossingGeometry.lean)
-/
@[path]
private lemma hexagonalStraightEdgeArc_range_chart_eq
  {x y : HexVertex}
-- given
  (hxy : hexagonalGraph.Adj x y) :
-- imply
  let e : hexagonalGraph.edgeSet := ⟨s(x, y), hxy⟩ let a := hexagonalEdgeChartEquiv.symm e Set.range (hexagonalStraightEdgeArc hxy) = Set.range (Path.segment (hexagonalPlaneVertex (a.1, false)) (hexagonalPlaneVertex (a.1 + hexagonalStep a.2, true))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalStraightEdgeArc_range_chart hxy

/--
[triHexStraightEdge_crossing_iff_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicCrossingGeometry.lean)
-/
@[path]
private lemma triHexStraightEdge_crossing_iff_dual_eq
  {x y : Site 2}
  {z w : HexVertex}
-- given
  (hxy : triangularGraph.Adj x y)
  (hzw : hexagonalGraph.Adj z w) :
-- imply
  (∃ t u, triangularStraightEdgeArc hxy t = hexagonalStraightEdgeArc hzw u) ↔ triHexDualEdgeEquiv ⟨s(x, y), hxy⟩ = ⟨s(z, w), hzw⟩ := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexStraightEdge_crossing_iff_dual hxy hzw


-- created on 2026-10-23
