import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexBrickDualInfiniteDomination
open Filter Finset MeasureTheory Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[hexagonalFreeInfinite_faceDual_le_wiredTriangularBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualInfiniteDomination.lean)
-/
@[path]
private lemma hexagonalFreeInfinite_faceDual_le_wiredTriangularBox_eq
  {N : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
-- given
  (hN : 1 ≤ N)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (hexagonal.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real (triHexFaceDualInnerEvent N A) ≤ activeBCMean (triangularBoxGraph N) (boundaryCliqueGraph (triHexBrickInnerBoundary N)) (fun _ => dualParam p q) q (A.indicator fun _ => (1 : Real)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalFreeInfinite_faceDual_le_wiredTriangularBox N hN hp hp1 hq hA

/--
[freeTriangularBox_le_hexagonalFreeInfinite_faceDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualInfiniteDomination.lean)
-/
@[path]
private lemma freeTriangularBox_le_hexagonalFreeInfinite_faceDual_eq
  {N : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (triangularBoxGraph N).edgeSet)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  activeBCMean (triangularBoxGraph N) ⊥ (fun _ => dualParam p q) q (A.indicator fun _ => (1 : Real)) ≤ (hexagonal.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real (triHexFaceDualInnerEvent N A) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.freeTriangularBox_le_hexagonalFreeInfinite_faceDual N hp hp1 hq hA


-- created on 2026-10-23
