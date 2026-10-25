import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareWiredPhaseTransport.Part2
open Filter Finset MeasureTheory Set SimpleGraph Topology StatMech StatMech.FrontierD


/--
[freeInfinite_faceDual_le_wiredFinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareWiredPhaseTransport.lean)
-/
@[path]
private lemma freeInfinite_faceDual_le_wiredFinite_eq
  {R N : Nat}
  {q : Real}
  {A : Set (ConfigSpace (FK.boxGraph 2 R).edgeSet)}
-- given
  (hRN : R ≤ N)
  (hN : 1 ≤ N)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  ((FK.freeInfiniteVolume 2 (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).1 (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).2 (zero_lt_one.trans_le hq) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))).real (fkSquareFaceDualInnerEvent R A) ≤ (FK.wiredFiniteMeasure 2 N (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).1 (selfDualPoint_mem_Ioo (zero_lt_one.trans_le hq)).2 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (FK.boxRestrict 2 R ⁻¹' (restrictActive (FK.boxGraph 2 R) ⁻¹' A)) := by
-- proof
  apply StatMech.FrontierD.freeInfinite_faceDual_le_wiredFinite hRN hN hq hA

/--
[fkSquare_openSub_extendActive_restrictActive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareWiredPhaseTransport.lean)
-/
@[path]
private lemma fkSquare_openSub_extendActive_restrictActive_eq
  {N : Nat}
  {eta : ConfigSpace (Sym2 (FK.boxVerts 2 N))} :
-- imply
  openSub (FK.boxGraph 2 N) (extendActive (FK.boxGraph 2 N) (restrictActive (FK.boxGraph 2 N) eta)) = openSub (FK.boxGraph 2 N) eta := by
-- proof
  apply StatMech.FrontierD.fkSquare_openSub_extendActive_restrictActive N eta

/--
[fkSquareActiveConnToBoundaryEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareWiredPhaseTransport.lean)
-/
@[path]
private lemma fkSquareActiveConnToBoundaryEvent_isIncreasing_eq
  {N : Nat}
  {x : FK.boxVerts 2 N} :
-- imply
  IsIncreasing (fkSquareActiveConnToBoundaryEvent N x) := by
-- proof
  apply StatMech.FrontierD.fkSquareActiveConnToBoundaryEvent_isIncreasing N x

/--
[fkSquare_activeConnToBoundary_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareWiredPhaseTransport.lean)
-/
@[path]
private lemma fkSquare_activeConnToBoundary_cylinder_eq
  {N : Nat}
  {x : FK.boxVerts 2 N} :
-- imply
  FK.boxRestrict 2 N ⁻¹' (restrictActive (FK.boxGraph 2 N) ⁻¹' fkSquareActiveConnToBoundaryEvent N x) = {omega : ConfigSpace (Sym2 (Site 2)) | IsingFK.ConnToBdry (FK.boxGraph 2 N) (FK.boxBoundary 2 N) (FK.boxRestrict 2 N omega) x} := by
-- proof
  apply StatMech.FrontierD.fkSquare_activeConnToBoundary_cylinder N x

/--
[fkSquare_faceDualInnerEvent_connToBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareWiredPhaseTransport.lean)
-/
@[path]
private lemma fkSquare_faceDualInnerEvent_connToBoundary_eq
  {N : Nat}
  {x : FK.boxVerts 2 N} :
-- imply
  fkSquareFaceDualInnerEvent N (fkSquareActiveConnToBoundaryEvent N x) = {omega : ConfigSpace (Sym2 (Site 2)) | IsingFK.ConnToBdry (FK.boxGraph 2 N) (FK.boxBoundary 2 N) (FK.boxRestrict 2 N (fci_faceDualConfig omega)) x} := by
-- proof
  apply StatMech.FrontierD.fkSquare_faceDualInnerEvent_connToBoundary N x


-- created on 2026-10-23
