import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactEnergy
open StatMech StatMech.Universality


/--
[fkIsingSquareRadialPatch_normSq_full_le_two_mul_diagonalPrimitiveVariation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactEnergy.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_normSq_full_le_two_mul_diagonalPrimitiveVariation_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi : i < m)
  (hj : j < m) :
-- imply
  Complex.normSq (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i, hi⟩ ⟨j, hj⟩) ≤ 2 * (|fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) (j + 1) - fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j| + |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j - fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1)|) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_normSq_full_le_two_mul_diagonalPrimitiveVariation n m hn hm hmpos i j hi hj

/--
[fkIsingSquareRadialPatch_normSq_full_le_two_mul_cellDiagonalVariation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactEnergy.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_normSq_full_le_two_mul_cellDiagonalVariation_eq
  {n m : Nat}
  {i j : Fin m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m) :
-- imply
  Complex.normSq (fkIsingSquareRadialPatchFullObservable n m hn hm i j) ≤ 2 * fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation n m hn hm hmpos i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_normSq_full_le_two_mul_cellDiagonalVariation n m hn hm hmpos i j

/--
[fkIsingSquareRadialPatch_two_mul_normSq_full_eq_cellTotalVariation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactEnergy.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_two_mul_normSq_full_eq_cellTotalVariation_eq
  {n m : Nat}
  {i j : Fin m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m) :
-- imply
  2 * Complex.normSq (fkIsingSquareRadialPatchFullObservable n m hn hm i j) = fkIsingSquareRadialPatchPrimitiveCellTotalVariation n m hn hm hmpos i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_two_mul_normSq_full_eq_cellTotalVariation n m hn hm hmpos i j

/--
[fkIsingSquareRadialPatch_physicalNormalized_normSq_sum_eq_totalVariation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactEnergy.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_physicalNormalized_normSq_sum_eq_totalVariation_eq
  {n m : Nat}
  {mesh : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hmesh : 0 < mesh) :
-- imply
  mesh ^ 2 * ∑ i : Fin m, ∑ j : Fin m, Complex.normSq (fkIsingSquareRadialPatchFullObservable n m hn hm i j / (Real.sqrt (2 * mesh) : Complex)) = mesh / 4 * ∑ i : Fin m, ∑ j : Fin m, fkIsingSquareRadialPatchPrimitiveCellTotalVariation n m hn hm hmpos i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_physicalNormalized_normSq_sum_eq_totalVariation n m mesh hn hm hmpos hmesh

/--
[fkIsingSquareRadialPatch_physicalNormalized_normSq_sum_le_diagonalVariation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactEnergy.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_physicalNormalized_normSq_sum_le_diagonalVariation_eq
  {n m : Nat}
  {mesh : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hmesh : 0 < mesh) :
-- imply
  mesh ^ 2 * ∑ i : Fin m, ∑ j : Fin m, Complex.normSq (fkIsingSquareRadialPatchFullObservable n m hn hm i j / (Real.sqrt (2 * mesh) : Complex)) ≤ mesh * ∑ i : Fin m, ∑ j : Fin m, fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation n m hn hm hmpos i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_physicalNormalized_normSq_sum_le_diagonalVariation n m mesh hn hm hmpos hmesh

/--
[fkIsingSquareRadialPatch_physicalNormalized_normSq_sum_le_of_cellVariation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactEnergy.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_physicalNormalized_normSq_sum_le_of_cellVariation_eq
  {n m : Nat}
  {mesh B L : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hmesh : 0 < mesh)
  (hB : 0 ≤ B)
  (hscale : mesh * (m : Real) ≤ L)
  (hvariation : ∀ i j : Fin m, fkIsingSquareRadialPatchPrimitiveCellTotalVariation n m hn hm hmpos i j ≤ 4 * B * mesh) :
-- imply
  mesh ^ 2 * ∑ i : Fin m, ∑ j : Fin m, Complex.normSq (fkIsingSquareRadialPatchFullObservable n m hn hm i j / (Real.sqrt (2 * mesh) : Complex)) ≤ B * L ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_physicalNormalized_normSq_sum_le_of_cellVariation n m mesh B L hn hm hmpos hmesh hB hscale hvariation


-- created on 2026-10-23
