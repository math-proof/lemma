import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGenericIntegration.Part3
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareFullCoordinateOneForm


/--
[primitiveNat_horizontal_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGenericIntegration.lean)
-/
@[path]
private lemma primitiveNat_horizontal_increment_eq
  {n : Nat}
  {A : FKIsingSquareFullCoordinateOneForm n}
  {i j : Nat} :
-- imply
  A.primitiveNat (i + 1) j - A.primitiveNat i j = A.horizontalNat i j := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullCoordinateOneForm.primitiveNat_horizontal_increment A i j

/--
[primitiveNat_vertical_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGenericIntegration.lean)
-/
@[path]
private lemma primitiveNat_vertical_increment_eq
  {n : Nat}
  {A : FKIsingSquareFullCoordinateOneForm n}
  {i j : Nat}
-- given
  (h0 : FKIsingSquareFullDiamond n (FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate n i j))
  (h1 : FKIsingSquareFullDiamond n (FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate n i (j + 1))) :
-- imply
  A.primitiveNat i (j + 1) - A.primitiveNat i j = A.verticalNat i j := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullCoordinateOneForm.primitiveNat_vertical_increment A i j h0 h1

/--
[coordinatePrimitive_horizontal_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGenericIntegration.lean)
-/
@[path]
private lemma coordinatePrimitive_horizontal_increment_eq
  {n : Nat}
  {A : FKIsingSquareFullCoordinateOneForm n}
  {q : Int × Int}
-- given
  (hq : FKIsingSquareFullDiamond n q) :
-- imply
  A.coordinatePrimitive (q.1 + 1, q.2) - A.coordinatePrimitive q = A.horizontal q := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullCoordinateOneForm.coordinatePrimitive_horizontal_increment A q hq

/--
[coordinatePrimitive_vertical_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGenericIntegration.lean)
-/
@[path]
private lemma coordinatePrimitive_vertical_increment_eq
  {n : Nat}
  {A : FKIsingSquareFullCoordinateOneForm n}
  {q : Int × Int}
-- given
  (hq : FKIsingSquareFullDiamond n q)
  (hqN : FKIsingSquareFullDiamond n (q.1, q.2 + 1)) :
-- imply
  A.coordinatePrimitive (q.1, q.2 + 1) - A.coordinatePrimitive q = A.vertical q := by
-- proof
  apply StatMech.Universality.FKIsingSquareFullCoordinateOneForm.coordinatePrimitive_vertical_increment A q hq hqN

/--
[fkIsingSquareFullBoxCoordinateOneForm_coordinatePrimitive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGenericIntegration.lean)
-/
@[path]
private lemma fkIsingSquareFullBoxCoordinateOneForm_coordinatePrimitive_eq
  {n : Nat}
  {q : Int × Int}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareFullBoxCoordinateOneForm n hn).coordinatePrimitive q = FKIsingSquareFullIntegratedPrimitive.coordinatePrimitive n hn q := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullBoxCoordinateOneForm_coordinatePrimitive n hn q

/--
[fkIsingSquareFullBoxCoordinateOneForm_vertexPrimitive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGenericIntegration.lean)
-/
@[path]
private lemma fkIsingSquareFullBoxCoordinateOneForm_vertexPrimitive_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareFullBoxCoordinateOneForm n hn).vertexPrimitive x = FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn x := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullBoxCoordinateOneForm_vertexPrimitive n hn x

/--
[fkIsingSquareFullBoxCoordinateOneForm_facePrimitive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGenericIntegration.lean)
-/
@[path]
private lemma fkIsingSquareFullBoxCoordinateOneForm_facePrimitive_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareFullBoxCoordinateOneForm n hn).facePrimitive c = FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn c := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullBoxCoordinateOneForm_facePrimitive n hn c


-- created on 2026-10-23
