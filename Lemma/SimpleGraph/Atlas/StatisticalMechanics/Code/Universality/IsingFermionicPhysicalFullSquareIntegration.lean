import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegration
open StatMech StatMech.Universality


/--
[fkIsingSquareFullRadialNodeCoordinate_mem_diamond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegration.lean)
-/
@[path]
private lemma fkIsingSquareFullRadialNodeCoordinate_mem_diamond_eq
  {n : Nat}
  {z : FKIsingSquareFullRadialNode n} :
-- imply
  FKIsingSquareFullDiamond n (fkIsingSquareFullRadialNodeCoordinate n z) := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullRadialNodeCoordinate_mem_diamond n z

/--
[fkIsingSquareFull_exists_node_of_mem_diamond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegration.lean)
-/
@[path]
private lemma fkIsingSquareFull_exists_node_of_mem_diamond_eq
  {n : Nat}
  {q : Int × Int}
-- given
  (hq : FKIsingSquareFullDiamond n q) :
-- imply
  ∃ z : FKIsingSquareFullRadialNode n, fkIsingSquareFullRadialNodeCoordinate n z = q := by
-- proof
  apply StatMech.Universality.fkIsingSquareFull_exists_node_of_mem_diamond n q hq

/--
[fkIsingSquareFullRadialNodeOfCoordinate_coordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegration.lean)
-/
@[path]
private lemma fkIsingSquareFullRadialNodeOfCoordinate_coordinate_eq
  {n : Nat}
  {q : Int × Int}
-- given
  (hq : FKIsingSquareFullDiamond n q) :
-- imply
  fkIsingSquareFullRadialNodeCoordinate n (fkIsingSquareFullRadialNodeOfCoordinate n q hq) = q := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullRadialNodeOfCoordinate_coordinate n q hq

/--
[fkIsingSquareFullRadialNodeOfCoordinate_inverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegration.lean)
-/
@[path]
private lemma fkIsingSquareFullRadialNodeOfCoordinate_inverse_eq
  {n : Nat}
  {z : FKIsingSquareFullRadialNode n} :
-- imply
  fkIsingSquareFullRadialNodeOfCoordinate n (fkIsingSquareFullRadialNodeCoordinate n z) (fkIsingSquareFullRadialNodeCoordinate_mem_diamond n z) = z := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullRadialNodeOfCoordinate_inverse n z

/--
[fkIsingSquareFullRadialCellOfCoordinate_even_side_coordinates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegration.lean)
-/
@[path]
private lemma fkIsingSquareFullRadialCellOfCoordinate_even_side_coordinates_eq
  {n : Nat}
  {q : Int × Int}
  {s : FKIsingMedialSide}
-- given
  (hn : 0 < n)
  (hq : FKIsingSquareFullDiamondCell n q)
  (heven : Even (q.1 + q.2)) :
-- imply
  fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn (fkIsingSquareInteriorRadialCellIncidence n hn (fkIsingSquareFullRadialCellOfCoordinate n q hq) s) = (match s with | .west | .south => q | .east | .north => (q.1 + 1, q.2 + 1)) ∧ fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn (fkIsingSquareInteriorRadialCellIncidence n hn (fkIsingSquareFullRadialCellOfCoordinate n q hq) s) = (match s with | .west | .north => (q.1 + 1, q.2) | .east | .south => (q.1, q.2 + 1)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullRadialCellOfCoordinate_even_side_coordinates n hn q hq heven s

/--
[fkIsingSquareFullRadialCellOfCoordinate_odd_side_coordinates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegration.lean)
-/
@[path]
private lemma fkIsingSquareFullRadialCellOfCoordinate_odd_side_coordinates_eq
  {n : Nat}
  {q : Int × Int}
  {s : FKIsingMedialSide}
-- given
  (hn : 0 < n)
  (hq : FKIsingSquareFullDiamondCell n q)
  (hodd : ¬ Even (q.1 + q.2)) :
-- imply
  fkIsingSquareInteriorRadialIncidenceEndpointCoordinate n hn (fkIsingSquareInteriorRadialCellIncidence n hn (fkIsingSquareFullRadialCellOfCoordinate n q hq) s) = (match s with | .west | .south => (q.1, q.2 + 1) | .east | .north => (q.1 + 1, q.2)) ∧ fkIsingSquareInteriorRadialIncidenceFaceCoordinate n hn (fkIsingSquareInteriorRadialCellIncidence n hn (fkIsingSquareFullRadialCellOfCoordinate n q hq) s) = (match s with | .west | .north => q | .east | .south => (q.1 + 1, q.2 + 1)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullRadialCellOfCoordinate_odd_side_coordinates n hn q hq hodd s

/--
[fkIsingSquareFullOrientedRadialIncrement_incidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegration.lean)
-/
@[path]
private lemma fkIsingSquareFullOrientedRadialIncrement_incidence_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareFullOrientedRadialIncrement n hn (.inl (fkIsingSquareInteriorRadialEndpoint n hn e)) (.inr (fkIsingSquareFullFaceOfRadialIncidence n hn e)) = fkIsingSquareInteriorRadialIncrement n hn e := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullOrientedRadialIncrement_incidence n hn e

/--
[fkIsingSquareFullOrientedRadialIncrement_incidence_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegration.lean)
-/
@[path]
private lemma fkIsingSquareFullOrientedRadialIncrement_incidence_reverse_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareFullOrientedRadialIncrement n hn (.inr (fkIsingSquareFullFaceOfRadialIncidence n hn e)) (.inl (fkIsingSquareInteriorRadialEndpoint n hn e)) = -fkIsingSquareInteriorRadialIncrement n hn e := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullOrientedRadialIncrement_incidence_reverse n hn e

/--
[fkIsingSquareFullOrientedRadialIncrement_antisymm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegration.lean)
-/
@[path]
private lemma fkIsingSquareFullOrientedRadialIncrement_antisymm_eq
  {n : Nat}
  {a b : FKIsingSquareFullRadialNode n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareFullOrientedRadialIncrement n hn a b = -fkIsingSquareFullOrientedRadialIncrement n hn b a := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullOrientedRadialIncrement_antisymm n hn a b

/--
[fkIsingSquareFullRadialNodeAtCoordinate_coordinate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegration.lean)
-/
@[path]
private lemma fkIsingSquareFullRadialNodeAtCoordinate_coordinate_eq
  {n : Nat}
  {q : Int × Int}
-- given
  (hq : FKIsingSquareFullDiamond n q) :
-- imply
  fkIsingSquareFullRadialNodeCoordinate n (fkIsingSquareFullRadialNodeAtCoordinate n q) = q := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullRadialNodeAtCoordinate_coordinate n q hq

/--
[fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegration.lean)
-/
@[path]
private lemma fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex_eq
  {n : Nat}
  {q : Int × Int}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (hq : FKIsingSquareFullDiamond n q)
  (hx : fkIsingSquareFullVertexCoordinate n x = q) :
-- imply
  fkIsingSquareFullRadialNodeAtCoordinate n q = .inl x := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullRadialNodeAtCoordinate_eq_vertex n q hq x hx

/--
[fkIsingSquareFullRadialNodeAtCoordinate_eq_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegration.lean)
-/
@[path]
private lemma fkIsingSquareFullRadialNodeAtCoordinate_eq_face_eq
  {n : Nat}
  {q : Int × Int}
  {c : FKIsingSquareFullFaceNode n}
-- given
  (hq : FKIsingSquareFullDiamond n q)
  (hc : fkIsingSquareFullFaceCoordinate n c = q) :
-- imply
  fkIsingSquareFullRadialNodeAtCoordinate n q = .inr c := by
-- proof
  apply StatMech.Universality.fkIsingSquareFullRadialNodeAtCoordinate_eq_face n q hq c hc

/--
[fkIsingSquareFull_increment_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegration.lean)
-/
@[path]
private lemma fkIsingSquareFull_increment_closed_eq
  {n : Nat}
  {q : Int × Int}
-- given
  (hn : 0 < n)
  (hq : FKIsingSquareFullDiamondCell n q) :
-- imply
  fkIsingSquareFullVerticalIncrement n hn q + fkIsingSquareFullHorizontalIncrement n hn (q.1, q.2 + 1) = fkIsingSquareFullHorizontalIncrement n hn q + fkIsingSquareFullVerticalIncrement n hn (q.1 + 1, q.2) := by
-- proof
  apply StatMech.Universality.fkIsingSquareFull_increment_closed n hn q hq


-- created on 2026-10-23
