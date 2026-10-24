import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingDiagonalReflectionInfinite
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierA


/--
[freeDomain_spinProd_le_freeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionInfinite.lean)
-/
@[path]
private lemma freeDomain_spinProd_le_freeState_eq
  {d : Nat}
  {K : Finset (Site d)}
  {beta : Real}
  {A : Finset (Site d)}
-- given
  (hbeta : 0 <= beta)
  (hA : A ⊆ K) :
-- imply
  isingExpectation (freeDomainGraph K) beta 0 (spinProd (freeDomainSpinSupport K A)) <= ∫ omega, spinProd A omega ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierA.freeDomain_spinProd_le_freeState K beta hbeta A hA

/--
[integral_freeState_spinProd_diagonalReflect_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionInfinite.lean)
-/
@[path]
private lemma integral_freeState_spinProd_diagonalReflect_le_eq
  {d : Nat}
  {i j : Fin d}
  {c : Int}
  {beta : Real}
  {a b : Site d}
-- given
  (hij : i ≠ j)
  (hbeta : 0 <= beta)
  (hal : a i - a j < c)
  (hbl : b i - b j < c)
  (hab : a ≠ b)
  (habR : a ≠ isingDiagonalReflect i j c b) :
-- imply
  (∫ omega, spinProd ({a, isingDiagonalReflect i j c b} : Finset (Site d)) omega ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) <= ∫ omega, spinProd ({a, b} : Finset (Site d)) omega ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierA.integral_freeState_spinProd_diagonalReflect_le i j hij c beta hbeta a b hal hbl hab habR

/--
[currentContinuityFreeTwoPoint_diagonalReflect_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionInfinite.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_diagonalReflect_le_eq
  {d : Nat}
  {i j : Fin d}
  {c : Int}
  {beta : Real}
  {a b : Site d}
-- given
  (hij : i ≠ j)
  (hbeta : 0 <= beta)
  (hal : a i - a j < c)
  (hbl : b i - b j < c)
  (hab : a ≠ b)
  (habR : a ≠ isingDiagonalReflect i j c b) :
-- imply
  currentContinuityFreeTwoPoint d beta a (isingDiagonalReflect i j c b) <= currentContinuityFreeTwoPoint d beta a b := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeTwoPoint_diagonalReflect_le i j hij c beta hbeta a b hal hbl hab habR

/--
[isingMergeCoordinates_apply_i](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionInfinite.lean)
-/
@[path]
private lemma isingMergeCoordinates_apply_i_eq
  {d : Nat}
  {i j : Fin d}
  {x : Site d} :
-- imply
  isingMergeCoordinates i j x i = x i + x j := by
-- proof
  apply StatMech.FrontierA.isingMergeCoordinates_apply_i i j x

/--
[isingMergeCoordinates_apply_j](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionInfinite.lean)
-/
@[path]
private lemma isingMergeCoordinates_apply_j_eq
  {d : Nat}
  {i j : Fin d}
  {x : Site d}
-- given
  (hij : i ≠ j) :
-- imply
  isingMergeCoordinates i j x j = 0 := by
-- proof
  apply StatMech.FrontierA.isingMergeCoordinates_apply_j i j hij x

/--
[isingDiagonalReflect_self_eq_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionInfinite.lean)
-/
@[path]
private lemma isingDiagonalReflect_self_eq_merge_eq
  {d : Nat}
  {i j : Fin d}
  {x : Site d}
-- given
  (hij : i ≠ j) :
-- imply
  isingDiagonalReflect i j (x i) x = isingMergeCoordinates i j x := by
-- proof
  apply StatMech.FrontierA.isingDiagonalReflect_self_eq_merge i j hij x

/--
[currentContinuityFreeTwoPoint_mergeCoordinates_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDiagonalReflectionInfinite.lean)
-/
@[path]
private lemma currentContinuityFreeTwoPoint_mergeCoordinates_le_eq
  {d : Nat}
  {i j : Fin d}
  {beta : Real}
  {x : Site d}
-- given
  (hij : i ≠ j)
  (hbeta : 0 <= beta)
  (hi : 0 < x i)
  (hj : 0 <= x j) :
-- imply
  currentContinuityFreeTwoPoint d beta (Percolation.origin d) (isingMergeCoordinates i j x) <= currentContinuityFreeTwoPoint d beta (Percolation.origin d) x := by
-- proof
  apply StatMech.FrontierA.currentContinuityFreeTwoPoint_mergeCoordinates_le i j hij beta hbeta x hi hj


-- created on 2026-10-23
