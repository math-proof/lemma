import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.TriHexPeriodicStraightIntersection
open Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triangularCanonicalSegment_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicStraightIntersection.lean)
-/
@[path]
private lemma triangularCanonicalSegment_re_eq
  {x : Site 2}
  {i : Fin 3}
  {t : unitInterval} :
-- imply
  (Path.segment (triangularPlaneVertex x) (triangularPlaneVertex (x + triangularStep i)) t).re = (x 0 : Real) + (t : Real) * (triangularStep i 0 : Real) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularCanonicalSegment_re x i t

/--
[triangularCanonicalSegment_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicStraightIntersection.lean)
-/
@[path]
private lemma triangularCanonicalSegment_im_eq
  {x : Site 2}
  {i : Fin 3}
  {t : unitInterval} :
-- imply
  (Path.segment (triangularPlaneVertex x) (triangularPlaneVertex (x + triangularStep i)) t).im = (x 1 : Real) + (t : Real) * (triangularStep i 1 : Real) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularCanonicalSegment_im x i t

/--
[triangularCanonicalSegments_commonEndpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicStraightIntersection.lean)
-/
@[path]
private lemma triangularCanonicalSegments_commonEndpoint_eq
  {x z : Site 2}
  {i j : Fin 3}
  {p : Complex}
-- given
  (hp : p ∈ Set.range (Path.segment (triangularPlaneVertex x) (triangularPlaneVertex (x + triangularStep i))))
  (hq : p ∈ Set.range (Path.segment (triangularPlaneVertex z) (triangularPlaneVertex (z + triangularStep j)))) :
-- imply
  x = z ∨ x = z + triangularStep j ∨ x + triangularStep i = z ∨ x + triangularStep i = z + triangularStep j := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularCanonicalSegments_commonEndpoint x z i j p hp hq

/--
[triangularSegment_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicStraightIntersection.lean)
-/
@[path]
private lemma triangularSegment_re_eq
  {x y : Site 2}
  {t : unitInterval} :
-- imply
  (Path.segment (triangularPlaneVertex x) (triangularPlaneVertex y) t).re = (t : Real) * ((y 0 : Real) - (x 0 : Real)) + (x 0 : Real) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularSegment_re x y t

/--
[triangularSegment_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicStraightIntersection.lean)
-/
@[path]
private lemma triangularSegment_im_eq
  {x y : Site 2}
  {t : unitInterval} :
-- imply
  (Path.segment (triangularPlaneVertex x) (triangularPlaneVertex y) t).im = (t : Real) * ((y 1 : Real) - (x 1 : Real)) + (x 1 : Real) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularSegment_im x y t

/--
[mem_range_triangularSegment_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicStraightIntersection.lean)
-/
@[path]
private lemma mem_range_triangularSegment_symm_eq
  {x y : Site 2}
  {p : Complex}
-- given
  (hp : p ∈ Set.range (Path.segment (triangularPlaneVertex x) (triangularPlaneVertex y))) :
-- imply
  p ∈ Set.range (Path.segment (triangularPlaneVertex y) (triangularPlaneVertex x)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.mem_range_triangularSegment_symm x y hp

/--
[triangularNeighborSegments_inter_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicStraightIntersection.lean)
-/
@[path]
private lemma triangularNeighborSegments_inter_eq_eq
  {v a b : Site 2}
  {p : Complex}
-- given
  (hva : triangularGraph.Adj v a)
  (hvb : triangularGraph.Adj v b)
  (hab : Ne a b)
  (hpa : p ∈ Set.range (Path.segment (triangularPlaneVertex v) (triangularPlaneVertex a)))
  (hpb : p ∈ Set.range (Path.segment (triangularPlaneVertex v) (triangularPlaneVertex b))) :
-- imply
  p = triangularPlaneVertex v := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularNeighborSegments_inter_eq hva hvb hab hpa hpb

/--
[triangularStraightEdgeIntersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicStraightIntersection.lean)
-/
@[path]
private lemma triangularStraightEdgeIntersection_eq :
-- imply
  TriangularStraightEdgeIntersectionProperty := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularStraightEdgeIntersection

/--
[hexagonalPlaneVertex_re_scaled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicStraightIntersection.lean)
-/
@[path]
private lemma hexagonalPlaneVertex_re_scaled_eq
  {u : HexVertex} :
-- imply
  (hexagonalPlaneVertex u : Complex).re = (hexagonalScaledCoordinate u 0 : Real) / 3 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalPlaneVertex_re_scaled u

/--
[hexagonalPlaneVertex_im_scaled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicStraightIntersection.lean)
-/
@[path]
private lemma hexagonalPlaneVertex_im_scaled_eq
  {u : HexVertex} :
-- imply
  (hexagonalPlaneVertex u : Complex).im = (hexagonalScaledCoordinate u 1 : Real) / 3 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalPlaneVertex_im_scaled u

/--
[hexagonalSegment_re_scaled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicStraightIntersection.lean)
-/
@[path]
private lemma hexagonalSegment_re_scaled_eq
  {u v : HexVertex}
  {t : unitInterval} :
-- imply
  3 * (Path.segment (hexagonalPlaneVertex u) (hexagonalPlaneVertex v) t).re = (t : Real) * ((hexagonalScaledCoordinate v 0 : Real) - (hexagonalScaledCoordinate u 0 : Real)) + (hexagonalScaledCoordinate u 0 : Real) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalSegment_re_scaled u v t

/--
[hexagonalSegment_im_scaled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicStraightIntersection.lean)
-/
@[path]
private lemma hexagonalSegment_im_scaled_eq
  {u v : HexVertex}
  {t : unitInterval} :
-- imply
  3 * (Path.segment (hexagonalPlaneVertex u) (hexagonalPlaneVertex v) t).im = (t : Real) * ((hexagonalScaledCoordinate v 1 : Real) - (hexagonalScaledCoordinate u 1 : Real)) + (hexagonalScaledCoordinate u 1 : Real) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalSegment_im_scaled u v t

/--
[hexagonalCanonicalSegments_commonEndpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicStraightIntersection.lean)
-/
@[path]
private lemma hexagonalCanonicalSegments_commonEndpoint_eq
  {x z : Site 2}
  {i j : Fin 3}
  {p : Complex}
-- given
  (hp : p ∈ Set.range (Path.segment (hexagonalPlaneVertex (x, false)) (hexagonalPlaneVertex (x + hexagonalStep i, true))))
  (hq : p ∈ Set.range (Path.segment (hexagonalPlaneVertex (z, false)) (hexagonalPlaneVertex (z + hexagonalStep j, true)))) :
-- imply
  (x, false) = (z, false) ∨ (x + hexagonalStep i, true) = (z + hexagonalStep j, true) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalCanonicalSegments_commonEndpoint x z i j p hp hq

/--
[mem_range_hexagonalSegment_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicStraightIntersection.lean)
-/
@[path]
private lemma mem_range_hexagonalSegment_symm_eq
  {u v : HexVertex}
  {p : Complex}
-- given
  (hp : p ∈ Set.range (Path.segment (hexagonalPlaneVertex u) (hexagonalPlaneVertex v))) :
-- imply
  p ∈ Set.range (Path.segment (hexagonalPlaneVertex v) (hexagonalPlaneVertex u)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.mem_range_hexagonalSegment_symm u v hp

/--
[hexagonalNeighborSegments_inter_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicStraightIntersection.lean)
-/
@[path]
private lemma hexagonalNeighborSegments_inter_eq_eq
  {v a b : HexVertex}
  {p : Complex}
-- given
  (hva : hexagonalGraph.Adj v a)
  (hvb : hexagonalGraph.Adj v b)
  (hab : Ne a b)
  (hpa : p ∈ Set.range (Path.segment (hexagonalPlaneVertex v) (hexagonalPlaneVertex a)))
  (hpb : p ∈ Set.range (Path.segment (hexagonalPlaneVertex v) (hexagonalPlaneVertex b))) :
-- imply
  p = hexagonalPlaneVertex v := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalNeighborSegments_inter_eq hva hvb hab hpa hpb

/--
[hexagonalStraightEdgeIntersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicStraightIntersection.lean)
-/
@[path]
private lemma hexagonalStraightEdgeIntersection_eq :
-- imply
  HexagonalStraightEdgeIntersectionProperty := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalStraightEdgeIntersection


-- created on 2026-10-23
