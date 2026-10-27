import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalPrimitiveMacroIncrement
open StatMech StatMech.Universality


/--
[fkIsingSquareBoundaryLayerRadialCell_increment_eq_normSq_full_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalPrimitiveMacroIncrement.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayerRadialCell_increment_eq_normSq_full_projection_eq
  {n : Nat}
  {C : FKIsingSquareInteriorRadialCell n}
  {s : FKIsingMedialSide}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBoundaryLayerRadialIncrement n hn (fkIsingSquareInteriorRadialCellIncidence n hn C s) = Complex.normSq (isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (C.1, s))) (fkIsingSquareBoundaryFullMedialObservable n hn C.1)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayerRadialCell_increment_eq_normSq_full_projection n hn C s

/--
[fkIsingSquareFullRadialCellOfCoordinate_axis_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalPrimitiveMacroIncrement.lean)
-/
@[path]
private lemma fkIsingSquareFullRadialCellOfCoordinate_axis_horizontal_eq
  {n : Nat}
  {q : Int × Int}
-- given
  (hq : FKIsingSquareFullDiamondCell n q)
  (heven : Even (q.1 + q.2)) :
-- imply
  (fkIsingSquareOrientedEdge n (fkIsingSquareFullRadialCellOfCoordinate n q hq).1).axis = .horizontal := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullRadialCellOfCoordinate_axis_horizontal n q hq heven

/--
[fkIsingSquareFullRadialCellOfCoordinate_axis_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalPrimitiveMacroIncrement.lean)
-/
@[path]
private lemma fkIsingSquareFullRadialCellOfCoordinate_axis_vertical_eq
  {n : Nat}
  {q : Int × Int}
-- given
  (hq : FKIsingSquareFullDiamondCell n q)
  (hodd : ¬ Even (q.1 + q.2)) :
-- imply
  (fkIsingSquareOrientedEdge n (fkIsingSquareFullRadialCellOfCoordinate n q hq).1).axis = .vertical := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullRadialCellOfCoordinate_axis_vertical n q hq hodd

/--
[FKIsingSquareFullCoordinateOneForm.coordinatePrimitive_even_northeast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalPrimitiveMacroIncrement.lean)
-/
@[path]
private lemma coordinatePrimitive_even_northeast_eq
  {n : Nat}
  {q : Int × Int}
-- given
  (hn : 0 < n)
  (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real)
  (hinc : forall C : FKIsingSquareInteriorRadialCell n, inc (fkIsingSquareInteriorRadialCellIncidence n hn C .west) + inc (fkIsingSquareInteriorRadialCellIncidence n hn C .east) = inc (fkIsingSquareInteriorRadialCellIncidence n hn C .south) + inc (fkIsingSquareInteriorRadialCellIncidence n hn C .north))
  (hq : FKIsingSquareFullDiamondCell n q)
  (heven : Even (q.1 + q.2)) :
-- imply
  let A := fkIsingSquareFullCoordinateOneFormOf n hn inc hinc let C := fkIsingSquareFullRadialCellOfCoordinate n q hq A.coordinatePrimitive (q.1 + 1, q.2 + 1) - A.coordinatePrimitive q = inc (fkIsingSquareInteriorRadialCellIncidence n hn C .west) - inc (fkIsingSquareInteriorRadialCellIncidence n hn C .north) := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullCoordinateOneForm.coordinatePrimitive_even_northeast n hn inc hinc q hq heven

/--
[FKIsingSquareFullCoordinateOneForm.coordinatePrimitive_odd_southeast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalPrimitiveMacroIncrement.lean)
-/
@[path]
private lemma coordinatePrimitive_odd_southeast_eq
  {n : Nat}
  {q : Int × Int}
-- given
  (hn : 0 < n)
  (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real)
  (hinc : forall C : FKIsingSquareInteriorRadialCell n, inc (fkIsingSquareInteriorRadialCellIncidence n hn C .west) + inc (fkIsingSquareInteriorRadialCellIncidence n hn C .east) = inc (fkIsingSquareInteriorRadialCellIncidence n hn C .south) + inc (fkIsingSquareInteriorRadialCellIncidence n hn C .north))
  (hq : FKIsingSquareFullDiamondCell n q)
  (hodd : ¬ Even (q.1 + q.2)) :
-- imply
  let A := fkIsingSquareFullCoordinateOneFormOf n hn inc hinc let C := fkIsingSquareFullRadialCellOfCoordinate n q hq A.coordinatePrimitive (q.1 + 1, q.2) - A.coordinatePrimitive (q.1, q.2 + 1) = inc (fkIsingSquareInteriorRadialCellIncidence n hn C .west) - inc (fkIsingSquareInteriorRadialCellIncidence n hn C .north) := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullCoordinateOneForm.coordinatePrimitive_odd_southeast n hn inc hinc q hq hodd

/--
[fkIsingSquareBoundaryLayer_coordinatePrimitive_even_northeast_eq_sq_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalPrimitiveMacroIncrement.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayer_coordinatePrimitive_even_northeast_eq_sq_im_eq
  {n : Nat}
  {q : Int × Int}
-- given
  (hn : 0 < n)
  (hq : FKIsingSquareFullDiamondCell n q)
  (heven : Even (q.1 + q.2)) :
-- imply
  let A := fkIsingSquareBoundaryLayerCoordinateOneForm n hn let C := fkIsingSquareFullRadialCellOfCoordinate n q hq A.coordinatePrimitive (q.1 + 1, q.2 + 1) - A.coordinatePrimitive q = ((fkIsingSquareBoundaryFullMedialObservable n hn C.1) ^ 2 * ((-1 + Complex.I) / 2)).im := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayer_coordinatePrimitive_even_northeast_eq_sq_im n hn q hq heven

/--
[fkIsingSquareBoundaryLayer_coordinatePrimitive_odd_southeast_eq_sq_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalPrimitiveMacroIncrement.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayer_coordinatePrimitive_odd_southeast_eq_sq_im_eq
  {n : Nat}
  {q : Int × Int}
-- given
  (hn : 0 < n)
  (hq : FKIsingSquareFullDiamondCell n q)
  (hodd : ¬ Even (q.1 + q.2)) :
-- imply
  let A := fkIsingSquareBoundaryLayerCoordinateOneForm n hn let C := fkIsingSquareFullRadialCellOfCoordinate n q hq A.coordinatePrimitive (q.1 + 1, q.2) - A.coordinatePrimitive (q.1, q.2 + 1) = ((fkIsingSquareBoundaryFullMedialObservable n hn C.1) ^ 2 * ((1 + Complex.I) / 2)).im := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayer_coordinatePrimitive_odd_southeast_eq_sq_im n hn q hq hodd


-- created on 2026-10-23
