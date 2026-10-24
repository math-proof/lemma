import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence
open StatMech StatMech.Universality


/--
[fkIsingSquareFullVertexCoordinate_sum_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIncidence.lean)
-/
@[path]
private lemma fkIsingSquareFullVertexCoordinate_sum_even_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n} :
-- imply
  Even ((fkIsingSquareFullVertexCoordinate n x).1 + (fkIsingSquareFullVertexCoordinate n x).2) := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullVertexCoordinate_sum_even n x

/--
[fkIsingSquareFullFaceCoordinate_sum_not_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIncidence.lean)
-/
@[path]
private lemma fkIsingSquareFullFaceCoordinate_sum_not_even_eq
  {n : Nat}
  {c : FKIsingSquareFullFaceNode n} :
-- imply
  ¬ Even ((fkIsingSquareFullFaceCoordinate n c).1 + (fkIsingSquareFullFaceCoordinate n c).2) := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullFaceCoordinate_sum_not_even n c

/--
[fkIsingSquareFull_exists_incidence_of_radiallyAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIncidence.lean)
-/
@[path]
private lemma fkIsingSquareFull_exists_incidence_of_radiallyAdjacent_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n)
  (h : fkIsingSquareFullFaceCoordinate n c = ((fkIsingSquareFullVertexCoordinate n x).1 + (1 : Int), (fkIsingSquareFullVertexCoordinate n x).2) ∨ fkIsingSquareFullFaceCoordinate n c = ((fkIsingSquareFullVertexCoordinate n x).1, (fkIsingSquareFullVertexCoordinate n x).2 + (1 : Int)) ∨ fkIsingSquareFullFaceCoordinate n c = ((fkIsingSquareFullVertexCoordinate n x).1 - (1 : Int), (fkIsingSquareFullVertexCoordinate n x).2) ∨ fkIsingSquareFullFaceCoordinate n c = ((fkIsingSquareFullVertexCoordinate n x).1, (fkIsingSquareFullVertexCoordinate n x).2 - (1 : Int))) :
-- imply
  ∃ e : FKIsingSquareInteriorRadialIncidence n hn, fkIsingSquareInteriorRadialEndpoint n hn e = x ∧ fkIsingSquareInteriorRadialFaceKey n hn e = fkIsingSquareInteriorCellKey n c := by
-- proof
  apply StatMech.Universality.fkIsingSquareFull_exists_incidence_of_radiallyAdjacent n hn x c h

/--
[fkIsingSquareFullIncidenceOfAdjacent_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIncidence.lean)
-/
@[path]
private lemma fkIsingSquareFullIncidenceOfAdjacent_endpoint_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n)
  (h : FKIsingSquareFullRadiallyAdjacent n x c) :
-- imply
  fkIsingSquareInteriorRadialEndpoint n hn (fkIsingSquareFullIncidenceOfAdjacent n hn x c h) = x := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullIncidenceOfAdjacent_endpoint n hn x c h

/--
[fkIsingSquareFullIncidenceOfAdjacent_faceKey](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIncidence.lean)
-/
@[path]
private lemma fkIsingSquareFullIncidenceOfAdjacent_faceKey_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n)
  (h : FKIsingSquareFullRadiallyAdjacent n x c) :
-- imply
  fkIsingSquareInteriorRadialFaceKey n hn (fkIsingSquareFullIncidenceOfAdjacent n hn x c h) = fkIsingSquareInteriorCellKey n c := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullIncidenceOfAdjacent_faceKey n hn x c h

/--
[fkIsingSquareFullIncidenceOfAdjacent_fullFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIncidence.lean)
-/
@[path]
private lemma fkIsingSquareFullIncidenceOfAdjacent_fullFace_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hn : 0 < n)
  (h : FKIsingSquareFullRadiallyAdjacent n x c) :
-- imply
  fkIsingSquareFullFaceOfRadialIncidence n hn (fkIsingSquareFullIncidenceOfAdjacent n hn x c h) = c := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullIncidenceOfAdjacent_fullFace n hn x c h

/--
[fkIsingSquareFullIncidenceOfAdjacent_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIncidence.lean)
-/
@[path]
private lemma fkIsingSquareFullIncidenceOfAdjacent_unique_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
  {c : FKIsingSquareFullFaceNode n}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n)
  (h : FKIsingSquareFullRadiallyAdjacent n x c)
  (hend : fkIsingSquareInteriorRadialEndpoint n hn e = x)
  (hface : fkIsingSquareFullFaceOfRadialIncidence n hn e = c) :
-- imply
  e = fkIsingSquareFullIncidenceOfAdjacent n hn x c h := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullIncidenceOfAdjacent_unique n hn x c h e hend hface

/--
[fkIsingSquareFullVertexCoordinate_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIncidence.lean)
-/
@[path]
private lemma fkIsingSquareFullVertexCoordinate_injective_eq
  {n : Nat} :
-- imply
  Function.Injective (fkIsingSquareFullVertexCoordinate n) := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullVertexCoordinate_injective n

/--
[fkIsingSquareFullFaceCoordinate_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIncidence.lean)
-/
@[path]
private lemma fkIsingSquareFullFaceCoordinate_injective_eq
  {n : Nat} :
-- imply
  Function.Injective (fkIsingSquareFullFaceCoordinate n) := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullFaceCoordinate_injective n

/--
[fkIsingSquareFullRadialNodeCoordinate_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIncidence.lean)
-/
@[path]
private lemma fkIsingSquareFullRadialNodeCoordinate_injective_eq
  {n : Nat} :
-- imply
  Function.Injective (fkIsingSquareFullRadialNodeCoordinate n) := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullRadialNodeCoordinate_injective n

/--
[fkIsingSquareFull_radiallyAdjacent_of_incidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIncidence.lean)
-/
@[path]
private lemma fkIsingSquareFull_radiallyAdjacent_of_incidence_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n) :
-- imply
  FKIsingSquareFullRadiallyAdjacent n (fkIsingSquareInteriorRadialEndpoint n hn e) (fkIsingSquareFullFaceOfRadialIncidence n hn e) := by
-- proof
  apply StatMech.Universality.fkIsingSquareFull_radiallyAdjacent_of_incidence n hn e

/--
[fkIsingSquareFullIncidenceOfAdjacent_of_incidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIncidence.lean)
-/
@[path]
private lemma fkIsingSquareFullIncidenceOfAdjacent_of_incidence_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareFullIncidenceOfAdjacent n hn (fkIsingSquareInteriorRadialEndpoint n hn e) (fkIsingSquareFullFaceOfRadialIncidence n hn e) (fkIsingSquareFull_radiallyAdjacent_of_incidence n hn e) = e := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullIncidenceOfAdjacent_of_incidence n hn e


-- created on 2026-10-23
