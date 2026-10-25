import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryDistance
open StatMech StatMech.Universality


/--
[fkIsingSquareRadialPatchPrimalBoundaryDistance_ge_of_coordinate_margin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryDistance.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalBoundaryDistance_ge_of_coordinate_margin_eq
  {n m r : Nat}
  {p : FKIsingSquareRadialPatchPrimalNode m}
-- given
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hi0 : r ≤ p.1.1.1)
  (hi1 : p.1.1.1 + r < m)
  (hj0 : r ≤ p.1.2.1)
  (hj1 : p.1.2.1 + r < m) :
-- imply
  r ≤ fkIsingSquareRadialPatchPrimalBoundaryDistance n m hm (by omega) p := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalBoundaryDistance_ge_of_coordinate_margin n m r hm hm2 p hi0 hi1 hj0 hj1

/--
[fkIsingSquareRadialPatchDualBoundaryDistance_ge_of_coordinate_margin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBoundaryDistance.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDualBoundaryDistance_ge_of_coordinate_margin_eq
  {m r : Nat}
  {p : FKIsingSquareRadialPatchDualNode m}
-- given
  (hm2 : 2 ≤ m)
  (hi0 : r ≤ p.1.1.1)
  (hi1 : p.1.1.1 + r < m)
  (hj0 : r ≤ p.1.2.1)
  (hj1 : p.1.2.1 + r < m) :
-- imply
  r ≤ fkIsingSquareRadialPatchDualBoundaryDistance m hm2 p := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDualBoundaryDistance_ge_of_coordinate_margin m r hm2 p hi0 hi1 hj0 hj1


-- created on 2026-10-23
