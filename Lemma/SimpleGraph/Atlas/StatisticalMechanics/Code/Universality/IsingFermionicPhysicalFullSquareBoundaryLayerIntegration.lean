import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerIntegration.Part3
open StatMech StatMech.Universality


/--
[fkIsingSquareFullOrientedRadialIncrementOf_incidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerIntegration.lean)
-/
@[path]
private lemma fkIsingSquareFullOrientedRadialIncrementOf_incidence_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n)
  (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real) :
-- imply
  fkIsingSquareFullOrientedRadialIncrementOf n hn inc (.inl (fkIsingSquareInteriorRadialEndpoint n hn e)) (.inr (fkIsingSquareFullFaceOfRadialIncidence n hn e)) = inc e := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullOrientedRadialIncrementOf_incidence n hn inc e

/--
[fkIsingSquareFullOrientedRadialIncrementOf_incidence_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerIntegration.lean)
-/
@[path]
private lemma fkIsingSquareFullOrientedRadialIncrementOf_incidence_reverse_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n)
  (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real) :
-- imply
  fkIsingSquareFullOrientedRadialIncrementOf n hn inc (.inr (fkIsingSquareFullFaceOfRadialIncidence n hn e)) (.inl (fkIsingSquareInteriorRadialEndpoint n hn e)) = -inc e := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullOrientedRadialIncrementOf_incidence_reverse n hn inc e

/--
[fkIsingSquareFull_increment_closed_of](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerIntegration.lean)
-/
@[path]
private lemma fkIsingSquareFull_increment_closed_of_eq
  {n : Nat}
  {q : Int × Int}
-- given
  (hn : 0 < n)
  (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real)
  (hinc : forall C : FKIsingSquareInteriorRadialCell n, inc (fkIsingSquareInteriorRadialCellIncidence n hn C .west) + inc (fkIsingSquareInteriorRadialCellIncidence n hn C .east) = inc (fkIsingSquareInteriorRadialCellIncidence n hn C .south) + inc (fkIsingSquareInteriorRadialCellIncidence n hn C .north))
  (hq : FKIsingSquareFullDiamondCell n q) :
-- imply
  fkIsingSquareFullVerticalIncrementOf n hn inc q + fkIsingSquareFullHorizontalIncrementOf n hn inc (q.1, q.2 + 1) = fkIsingSquareFullHorizontalIncrementOf n hn inc q + fkIsingSquareFullVerticalIncrementOf n hn inc (q.1 + 1, q.2) := by
-- proof
  apply StatMech.Universality.fkIsingSquareFull_increment_closed_of n hn inc hinc q hq

/--
[fkIsingSquareFullCoordinateOneFormOf_face_sub_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerIntegration.lean)
-/
@[path]
private lemma fkIsingSquareFullCoordinateOneFormOf_face_sub_vertex_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n)
  (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real)
  (hinc : forall C : FKIsingSquareInteriorRadialCell n, inc (fkIsingSquareInteriorRadialCellIncidence n hn C .west) + inc (fkIsingSquareInteriorRadialCellIncidence n hn C .east) = inc (fkIsingSquareInteriorRadialCellIncidence n hn C .south) + inc (fkIsingSquareInteriorRadialCellIncidence n hn C .north)) :
-- imply
  let A := fkIsingSquareFullCoordinateOneFormOf n hn inc hinc A.facePrimitive (fkIsingSquareFullFaceOfRadialIncidence n hn e) - A.vertexPrimitive (fkIsingSquareInteriorRadialEndpoint n hn e) = inc e := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullCoordinateOneFormOf_face_sub_vertex n hn inc hinc e

/--
[fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerIntegration.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence n hn e) - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint n hn e) = fkIsingSquareBoundaryLayerRadialIncrement n hn e := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn e

/--
[fkIsingSquareBoundaryLayerCoordinateOneForm_vertex_le_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerIntegration.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayerCoordinateOneForm_vertex_le_face_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareInteriorRadialEndpoint n hn e) <= (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence n hn e) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayerCoordinateOneForm_vertex_le_face n hn e

/--
[fkIsingSquareBoundaryLayerRadialIncrement_perimeterInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerIntegration.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayerRadialIncrement_perimeterInterior_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareBoundaryLayerRadialIncrement n hn (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k) = fkIsingSquareBoundaryLayerInwardIncrement n hn side k := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayerRadialIncrement_perimeterInterior n hn side k

/--
[fkIsingSquareBoundaryLayerCoordinateOneForm_boundary_face_sub_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerIntegration.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayerCoordinateOneForm_boundary_face_sub_vertex_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence n hn (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k)) - (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareBoundaryVertex n (side, k)) = fkIsingSquareBoundaryLayerInwardIncrement n hn side k := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayerCoordinateOneForm_boundary_face_sub_vertex n hn side k

/--
[fkIsingSquareBoundaryLayerCoordinateOneForm_boundary_vertex_le_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerIntegration.lean)
-/
@[path]
private lemma fkIsingSquareBoundaryLayerCoordinateOneForm_boundary_vertex_le_face_eq
  {n : Nat}
  {side : FKIsingSquareBoundarySide}
  {k : Fin (2 * n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive (fkIsingSquareBoundaryVertex n (side, k)) <= (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive (fkIsingSquareFullFaceOfRadialIncidence n hn (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareBoundaryLayerCoordinateOneForm_boundary_vertex_le_face n hn side k


-- created on 2026-10-23
