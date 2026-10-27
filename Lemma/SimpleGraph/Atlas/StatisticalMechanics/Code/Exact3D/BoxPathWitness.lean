import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
open Filter StatMech StatMech.Exact3D


/--
[boxGraph_update_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma boxGraph_update_mem_box_eq
  {d n : ℕ}
  {x : Site d}
  {j : Fin d}
  {a : ℤ}
-- given
  (hx : x ∈ box d n)
  (ha : a.natAbs ≤ n) :
-- imply
  Function.update x j a ∈ box d n := by
-- proof
  apply StatMech.Exact3D.boxGraph_update_mem_box hx j ha

/--
[boxGraph_adj_update_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma boxGraph_adj_update_succ_eq
  {d n : ℕ}
  {x : Site d}
  {j : Fin d}
  {a : ℤ}
-- given
  (hx : x ∈ box d n)
  (ha : a.natAbs ≤ n)
  (ha1 : (a + 1).natAbs ≤ n) :
-- imply
  (FK.boxGraph d n).Adj ⟨Function.update x j a, boxGraph_update_mem_box hx j ha⟩ ⟨Function.update x j (a + 1), boxGraph_update_mem_box hx j ha1⟩ := by
-- proof
  apply StatMech.Exact3D.boxGraph_adj_update_succ hx j ha ha1

/--
[boxGraph_adj_boxVertStrictSectorPredecessor3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma boxGraph_adj_boxVertStrictSectorPredecessor3_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
  (hlt : ((v : Lattice.Site 3) (1 : Fin 3)) < ((v : Lattice.Site 3) (2 : Fin 3))) :
-- imply
  (FK.boxGraph 3 n).Adj (boxVertStrictSectorPredecessor3 v hvwedge hlt) v := by
-- proof
  apply StatMech.Exact3D.boxGraph_adj_boxVertStrictSectorPredecessor3 v hvwedge hlt

/--
[boxGraph_adj_boxVertStrictSectorYPredecessor3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma boxGraph_adj_boxVertStrictSectorYPredecessor3_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
  (hlt : ((v : Lattice.Site 3) (1 : Fin 3)) < ((v : Lattice.Site 3) (2 : Fin 3)))
  (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) :
-- imply
  (FK.boxGraph 3 n).Adj (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) v := by
-- proof
  apply StatMech.Exact3D.boxGraph_adj_boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos

/--
[boxGraph_adj_boxVertDiagonalPredecessor3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma boxGraph_adj_boxVertDiagonalPredecessor3_eq
  {n : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
  (hheight : boxVertTransverseHeight3 v ≠ 0)
  (hnotlt : ¬ ((v : Lattice.Site 3) (1 : Fin 3)) < ((v : Lattice.Site 3) (2 : Fin 3))) :
-- imply
  (FK.boxGraph 3 n).Adj (boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt) v := by
-- proof
  apply StatMech.Exact3D.boxGraph_adj_boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt

/--
[boxGraph_adj_boxVertInclLE_strictSectorPredecessor3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma boxGraph_adj_boxVertInclLE_strictSectorPredecessor3_eq
  {n M : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (h : n ≤ M)
  (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
  (hlt : ((v : Lattice.Site 3) (1 : Fin 3)) < ((v : Lattice.Site 3) (2 : Fin 3))) :
-- imply
  (FK.boxGraph 3 M).Adj (FK.boxVertInclLE 3 h (boxVertStrictSectorPredecessor3 v hvwedge hlt)) (FK.boxVertInclLE 3 h v) := by
-- proof
  apply StatMech.Exact3D.boxGraph_adj_boxVertInclLE_strictSectorPredecessor3 h v hvwedge hlt

/--
[boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3_eq
  {n M : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (h : n ≤ M)
  (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
  (hlt : ((v : Lattice.Site 3) (1 : Fin 3)) < ((v : Lattice.Site 3) (2 : Fin 3)))
  (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) :
-- imply
  (FK.boxGraph 3 M).Adj (FK.boxVertInclLE 3 h (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) (FK.boxVertInclLE 3 h v) := by
-- proof
  apply StatMech.Exact3D.boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3 h v hvwedge hlt hypos

/--
[boxGraph_adj_boxVertInclLE_diagonalPredecessor3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma boxGraph_adj_boxVertInclLE_diagonalPredecessor3_eq
  {n M : ℕ}
  {v : FK.boxVerts 3 n}
-- given
  (h : n ≤ M)
  (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
  (hheight : boxVertTransverseHeight3 v ≠ 0)
  (hnotlt : ¬ ((v : Lattice.Site 3) (1 : Fin 3)) < ((v : Lattice.Site 3) (2 : Fin 3))) :
-- imply
  (FK.boxGraph 3 M).Adj (FK.boxVertInclLE 3 h (boxVertDiagonalPredecessor3 v hvwedge hheight hnotlt)) (FK.boxVertInclLE 3 h v) := by
-- proof
  apply StatMech.Exact3D.boxGraph_adj_boxVertInclLE_diagonalPredecessor3 h v hvwedge hheight hnotlt

/--
[boxVertPositiveXFaceOrderedWedge3_lowerDoubledAdj_hasCoords3_yOrZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma boxVertPositiveXFaceOrderedWedge3_lowerDoubledAdj_hasCoords3_yOrZ_eq
  {n : ℕ}
  {v w : FK.boxVerts 3 n}
-- given
  (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
  (hwwedge : boxVertPositiveXFaceOrderedWedge3 n w)
  (hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v)
  (hadj : (FK.boxGraph 3 (2 * n)).Adj (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v)) :
-- imply
  boxVertHasCoords3 w (n : ℤ) (((v : Lattice.Site 3) (1 : Fin 3)) - 1) ((v : Lattice.Site 3) (2 : Fin 3)) ∨ boxVertHasCoords3 w (n : ℤ) ((v : Lattice.Site 3) (1 : Fin 3)) (((v : Lattice.Site 3) (2 : Fin 3)) - 1) := by
-- proof
  apply StatMech.Exact3D.boxVertPositiveXFaceOrderedWedge3_lowerDoubledAdj_hasCoords3_yOrZ hvwedge hwwedge hheight hadj

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical_of_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical_of_local_eq
-- given
  (hlocal : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonLocal) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical_of_local hlocal

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonAt_of_predecessorComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonAt_of_predecessorComparison_eq
  {β : ℝ}
  {hβpos : 0 < β}
  {n : ℕ}
-- given
  (hcmp : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonAt β hβpos n) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonAt β hβpos n := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonAt_of_predecessorComparison hcmp

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonAt_of_coordinateComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonAt_of_coordinateComparison_eq
  {β : ℝ}
  {hβpos : 0 < β}
  {n : ℕ}
-- given
  (hcmp : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonAt β hβpos n) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonAt β hβpos n := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonAt_of_coordinateComparison hcmp

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparison_of_predecessorComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparison_of_predecessorComparison_eq
-- given
  (hcmp : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparison_of_predecessorComparison hcmp

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparison_of_coordinateComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparison_of_coordinateComparison_eq
-- given
  (hcmp : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparison_of_coordinateComparison hcmp

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical_of_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical_of_local_eq
-- given
  (hlocal : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical_of_local hlocal

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical_of_predecessorLocal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical_of_predecessorLocal_eq
-- given
  (hlocal : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical_of_predecessorLocal hlocal

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_local_eq
-- given
  (hlocal : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_local hlocal

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentAt_of_coordinateCases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentAt_of_coordinateCases_eq
  {β : ℝ}
  {hβpos : 0 < β}
  {n : ℕ}
-- given
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonAt β hβpos n)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonAt β hβpos n)
  (hstrictY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonAt β hβpos n) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentAt β hβpos n := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentAt_of_coordinateCases hstrictZ hdiagY hstrictY

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_coordinateCases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_coordinateCases_eq
-- given
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonLocal) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_coordinateCases hstrictZ hdiagY hstrictY

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_coordinateCasesLocal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_coordinateCasesLocal_eq
-- given
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonLocal) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_coordinateCasesLocal hstrictZ hdiagY hstrictY

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_predecessorCases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_predecessorCases_eq
-- given
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_predecessorCases hstrictZ hdiagY hstrictY

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_predecessorCasesLocal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_predecessorCasesLocal_eq
-- given
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_predecessorCasesLocal hstrictZ hdiagY hstrictY

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_coordinateCases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_coordinateCases_eq
-- given
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
  (hstrictY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_coordinateCases hstrictZ hdiagY hstrictY

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_predecessorCases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_predecessorCases_eq
-- given
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
  (hstrictY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_predecessorCases hstrictZ hdiagY hstrictY

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescent_of_fullOneEdgeDescent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescent_of_fullOneEdgeDescent_eq
-- given
  (hone : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescentPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescent_of_fullOneEdgeDescent hone

/--
[freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullOneEdgeDescent_profileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullOneEdgeDescent_profileDoubleScale_eq
-- given
  (hone : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
-- imply
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjectionPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullOneEdgeDescent_profileDoubleScale hone hprofile

/--
[boxGraph_reachable_update_ascend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma boxGraph_reachable_update_ascend_eq
  {d n : ℕ}
  {x : Site d}
  {j : Fin d}
-- given
  (hx : x ∈ box d n) :
-- imply
  ∀ (k : ℕ) (a : ℤ) (ha : a.natAbs ≤ n) (hak : (a + (k : ℤ)).natAbs ≤ n), (FK.boxGraph d n).Reachable ⟨Function.update x j a, boxGraph_update_mem_box hx j ha⟩ ⟨Function.update x j (a + (k : ℤ)), boxGraph_update_mem_box hx j hak⟩ := by
-- proof
  apply StatMech.Exact3D.boxGraph_reachable_update_ascend hx j

/--
[boxGraph_reachable_update](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma boxGraph_reachable_update_eq
  {d n : ℕ}
  {x : Site d}
  {j : Fin d}
  {a : ℤ}
-- given
  (hx : x ∈ box d n)
  (ha : a.natAbs ≤ n) :
-- imply
  (FK.boxGraph d n).Reachable ⟨x, hx⟩ ⟨Function.update x j a, boxGraph_update_mem_box hx j ha⟩ := by
-- proof
  apply StatMech.Exact3D.boxGraph_reachable_update hx j ha

/--
[boxGraph_reachable_mixSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma boxGraph_reachable_mixSite_eq
  {d n : ℕ}
  {x y : Site d}
-- given
  (hx : x ∈ box d n)
  (hy : y ∈ box d n) :
-- imply
  ∀ k ≤ d, (FK.boxGraph d n).Reachable ⟨x, hx⟩ ⟨Percolation.mixSite x y k, Percolation.mixSite_mem_box hx hy k⟩ := by
-- proof
  apply StatMech.Exact3D.boxGraph_reachable_mixSite hx hy

/--
[boxGraph_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma boxGraph_reachable_eq
  {d n : ℕ}
  {x y : FK.boxVerts d n} :
-- imply
  (FK.boxGraph d n).Reachable x y := by
-- proof
  apply StatMech.Exact3D.boxGraph_reachable d n x y

/--
[finiteBoundaryGhostOriginalPathWitness_of_boxPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma finiteBoundaryGhostOriginalPathWitness_of_boxPath_eq
  {n : ℕ}
  {a b : FK.boxVerts 3 n}
  {p0 : (FK.boxGraph 3 n).Path a b} :
-- imply
  ∃ p : (Sharpness.withGhost (FK.boxGraph 3 n)).Path (some a) (some b), ∀ e : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset, 0 < p.1.edges.count e.1 → Sharpness.edgeInside (finiteBoundaryGhostOriginalSet 3 n) e.1 := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostOriginalPathWitness_of_boxPath p0

/--
[finiteBoundaryGhostOriginalPathWitness3D](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma finiteBoundaryGhostOriginalPathWitness3D_eq :
-- imply
  FiniteBoundaryGhostOriginalPathWitness3D := by
-- proof
  apply StatMech.Exact3D.finiteBoundaryGhostOriginalPathWitness3D

/--
[finiteQ2BoundaryVertexDenominatorPositiveSupportCurrentWitness_from_boxGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma finiteQ2BoundaryVertexDenominatorPositiveSupportCurrentWitness_from_boxGeometry_eq :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveSupportCurrentWitnessPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.finiteQ2BoundaryVertexDenominatorPositiveSupportCurrentWitness_from_boxGeometry

/--
[finiteQ2BoundaryVertexDenominatorPositive_from_boxGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma finiteQ2BoundaryVertexDenominatorPositive_from_boxGeometry_eq :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositivePositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.finiteQ2BoundaryVertexDenominatorPositive_from_boxGeometry

/--
[finiteQ2PositiveDenominatorComponentSumAbsorption_of_boxGeometry_componentSumAbsorption](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoxPathWitness.lean)
-/
@[path]
private lemma finiteQ2PositiveDenominatorComponentSumAbsorption_of_boxGeometry_componentSumAbsorption_eq
-- given
  (hsum : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentSumAbsorptionPositiveSubcritical) :
-- imply
  FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorptionPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.finiteQ2PositiveDenominatorComponentSumAbsorption_of_boxGeometry_componentSumAbsorption hsum


-- created on 2026-10-23
