import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleTopology
open StatMech StatMech.FrontierA


/--
[triangularTorusDirectionAngle_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleTopology.lean)
-/
@[path]
private lemma triangularTorusDirectionAngle_turn_eq
  {a b : Fin 6}
-- given
  (hne : b ≠ triangularTorusDirectionReverse a) :
-- imply
  (triangularTorusDirectionAngle b - triangularTorusDirectionAngle a).toReal = (triangularTorusTurnExponent a b : Real) * (Real.pi / 4) := by
-- proof
  apply StatMech.FrontierA.triangularTorusDirectionAngle_turn a b hne

/--
[triangularIntVector_arg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleTopology.lean)
-/
@[path]
private lemma triangularIntVector_arg_eq
  {a : Fin 6} :
-- imply
  (Complex.arg (triangularIntVector a) : Real.Angle) = triangularTorusDirectionAngle a := by
-- proof
  apply StatMech.FrontierA.triangularIntVector_arg a

/--
[triangularIntPoint_add_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleTopology.lean)
-/
@[path]
private lemma triangularIntPoint_add_sub_eq
  {p q : Int × Int} :
-- imply
  triangularIntPoint (p + q) - triangularIntPoint p = triangularIntPoint q := by
-- proof
  apply StatMech.FrontierA.triangularIntPoint_add_sub p q

/--
[triangularIntSimplePolygon_edgeVector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleTopology.lean)
-/
@[path]
private lemma triangularIntSimplePolygon_edgeVector_eq
  {n : Nat}
  [NeZero n]
  {i : Fin n}
-- given
  (direction : Fin n -> Fin 6)
  (hclosed : ∑ i, triangularIntStep (direction i) = 0)
  (hn : 3 <= n)
  (hinjective : Function.Injective (triangularIntPos direction)) :
-- imply
  (triangularIntSimplePolygon direction hclosed hn hinjective).edgeVector i = triangularIntVector (direction i) := by
-- proof
  apply StatMech.FrontierA.triangularIntSimplePolygon_edgeVector direction hclosed hn hinjective i

/--
[kwVectorTurnPhase_triangularIntVector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleTopology.lean)
-/
@[path]
private lemma kwVectorTurnPhase_triangularIntVector_eq
  {a b : Fin 6} :
-- imply
  kwVectorTurnPhase (triangularIntVector a) (triangularIntVector b) = kwAngleTurnPhase (triangularTorusDirectionAngle a) (triangularTorusDirectionAngle b) := by
-- proof
  apply StatMech.FrontierA.kwVectorTurnPhase_triangularIntVector a b

/--
[exists_triangularTorusTurnExponent_sum_eq_eight_mul_odd_of_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleTopology.lean)
-/
@[path]
private lemma exists_triangularTorusTurnExponent_sum_eq_eight_mul_odd_of_closed_eq
  {n : Nat}
  [NeZero n]
-- given
  (direction : Fin n -> Fin 6)
  (hnonbacktracking : forall k, direction (k + 1) ≠ triangularTorusDirectionReverse (direction k))
  (hclosed : ∑ i, triangularIntStep (direction i) = 0)
  (hn : 3 <= n)
  (hinjective : Function.Injective (triangularIntPos direction)) :
-- imply
  exists m : Int, (∑ k, triangularTorusTurnExponent (direction k) (direction (k + 1))) = 8 * (2 * m + 1) := by
-- proof
  apply StatMech.FrontierA.exists_triangularTorusTurnExponent_sum_eq_eight_mul_odd_of_closed direction hnonbacktracking hclosed hn hinjective


-- created on 2026-10-23
