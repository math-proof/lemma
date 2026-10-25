import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalPrimitiveBounds
open StatMech StatMech.Universality


/--
[fkIsingSquareInteriorRadialIncrement_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalPrimitiveBounds.lean)
-/
@[path]
private lemma fkIsingSquareInteriorRadialIncrement_le_one_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareInteriorRadialIncrement n hn e ≤ 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorRadialIncrement_le_one n hn e

/--
[abs_fkIsingSquareRadialPatchHorizontalSignedIncrement_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalPrimitiveBounds.lean)
-/
@[path]
private lemma abs_fkIsingSquareRadialPatchHorizontalSignedIncrement_le_one_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m) :
-- imply
  |fkIsingSquareRadialPatchHorizontalSignedIncrement n m hn hm hmpos i j| ≤ 1 := by
-- proof
  apply StatMech.Universality.abs_fkIsingSquareRadialPatchHorizontalSignedIncrement_le_one n m hn hm hmpos i j

/--
[abs_fkIsingSquareRadialPatchVerticalSignedIncrement_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalPrimitiveBounds.lean)
-/
@[path]
private lemma abs_fkIsingSquareRadialPatchVerticalSignedIncrement_le_one_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m) :
-- imply
  |fkIsingSquareRadialPatchVerticalSignedIncrement n m hn hm hmpos i j| ≤ 1 := by
-- proof
  apply StatMech.Universality.abs_fkIsingSquareRadialPatchVerticalSignedIncrement_le_one n m hn hm hmpos i j

/--
[abs_fkIsingSquareRadialPatchPrimitive_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalPrimitiveBounds.lean)
-/
@[path]
private lemma abs_fkIsingSquareRadialPatchPrimitive_le_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m) :
-- imply
  |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j| ≤ i + j := by
-- proof
  apply StatMech.Universality.abs_fkIsingSquareRadialPatchPrimitive_le n m hn hm hmpos i j


-- created on 2026-10-23
