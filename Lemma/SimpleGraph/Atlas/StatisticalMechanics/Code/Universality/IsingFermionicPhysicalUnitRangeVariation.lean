import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalUnitRangeVariation
open StatMech StatMech.Universality


/--
[fkIsingSquareRadialPatchPrimal_exists_orderedDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalUnitRangeVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimal_exists_orderedDual_eq
  {n m : Nat}
  {base : Real}
  {p : FKIsingSquareRadialPatchPrimalNode m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m) :
-- imply
  ∃ q : FKIsingSquareRadialPatchDualNode m, fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p ≤ fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimal_exists_orderedDual n m hn hm hm2 base p

/--
[fkIsingSquareRadialPatchDual_exists_orderedPrimal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalUnitRangeVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDual_exists_orderedPrimal_eq
  {n m : Nat}
  {base : Real}
  {q : FKIsingSquareRadialPatchDualNode m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m) :
-- imply
  ∃ p : FKIsingSquareRadialPatchPrimalNode m, fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p ≤ fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDual_exists_orderedPrimal n m hn hm hm2 base q

/--
[fkIsingSquareRadialPatch_unitRange_of_primalLower_dualUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalUnitRangeVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_unitRange_of_primalLower_dualUpper_eq
  {n m : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hprimalLower : ∀ p, 0 ≤ fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p)
  (hdualUpper : ∀ q, fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q ≤ 1) :
-- imply
  (∀ p, 0 ≤ fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p ∧ fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p ≤ 1) ∧ (∀ q, 0 ≤ fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q ∧ fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q ≤ 1) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_unitRange_of_primalLower_dualUpper n m hn hm hm2 base hprimalLower hdualUpper

/--
[fkIsingSquareRadialPatchPrimal_deepVariation_sq_le_of_unitRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalUnitRangeVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimal_deepVariation_sq_le_of_unitRange_eq
  {n m : Nat}
  {r : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hr : 0 < r)
  (hlower : ∀ p, 0 ≤ fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p)
  (hupper : ∀ p, fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p ≤ 1) :
-- imply
  (∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm hmpos r, |fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.snd - fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.fst|) ^ 2 ≤ 16 * (#(fkIsingSquareRadialPatchPrimalDeepDarts n m hm hmpos r) : Real) * (m : Real) ^ 2 / (r : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimal_deepVariation_sq_le_of_unitRange n m hn hm hmpos r hr base hlower hupper

/--
[fkIsingSquareRadialPatchDual_deepVariation_sq_le_of_unitRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalUnitRangeVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDual_deepVariation_sq_le_of_unitRange_eq
  {n m : Nat}
  {r : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hr : 0 < r)
  (hlower : ∀ p, 0 ≤ fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base p)
  (hupper : ∀ p, fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base p ≤ 1) :
-- imply
  (∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r, |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd - fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) ^ 2 ≤ 16 * (#(fkIsingSquareRadialPatchDualDeepDarts m hm2 r) : Real) * (m : Real) ^ 2 / (r : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDual_deepVariation_sq_le_of_unitRange n m hn hm hm2 r hr base hlower hupper

/--
[fkIsingSquareRadialPatchPrimal_physicalDeepVariation_sq_le_of_unitRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalUnitRangeVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimal_physicalDeepVariation_sq_le_of_unitRange_eq
  {n m : Nat}
  {r : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hr : 0 < r)
  (hlower : ∀ p, 0 ≤ fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p)
  (hupper : ∀ p, fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p ≤ 1) :
-- imply
  ((1 / (m : Real)) * ∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm hmpos r, |fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.snd - fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.fst|) ^ 2 ≤ 64 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimal_physicalDeepVariation_sq_le_of_unitRange n m hn hm hmpos r hr base hlower hupper

/--
[fkIsingSquareRadialPatchDual_physicalDeepVariation_sq_le_of_unitRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalUnitRangeVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDual_physicalDeepVariation_sq_le_of_unitRange_eq
  {n m : Nat}
  {r : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hr : 0 < r)
  (hlower : ∀ p, 0 ≤ fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base p)
  (hupper : ∀ p, fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base p ≤ 1) :
-- imply
  ((1 / (m : Real)) * ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r, |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd - fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) ^ 2 ≤ 64 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDual_physicalDeepVariation_sq_le_of_unitRange n m hn hm hm2 r hr base hlower hupper

/--
[fkIsingSquareRadialPatchPrimal_physicalDeepVariation_fixedFraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalUnitRangeVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimal_physicalDeepVariation_fixedFraction_eq
  {n m : Nat}
  {r : Nat}
  {base K : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hr : 0 < r)
  (hK : 0 ≤ K)
  (hmr : (m : Real) ≤ K * (r : Real))
  (hlower : ∀ p, 0 ≤ fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p)
  (hupper : ∀ p, fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p ≤ 1) :
-- imply
  ((1 / (m : Real)) * ∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm hmpos r, |fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.snd - fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.fst|) ^ 2 ≤ 64 * K ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimal_physicalDeepVariation_fixedFraction n m hn hm hmpos r hr base K hK hmr hlower hupper

/--
[fkIsingSquareRadialPatchDual_physicalDeepVariation_fixedFraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalUnitRangeVariation.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDual_physicalDeepVariation_fixedFraction_eq
  {n m : Nat}
  {r : Nat}
  {base K : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hr : 0 < r)
  (hK : 0 ≤ K)
  (hmr : (m : Real) ≤ K * (r : Real))
  (hlower : ∀ p, 0 ≤ fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base p)
  (hupper : ∀ p, fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base p ≤ 1) :
-- imply
  ((1 / (m : Real)) * ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r, |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd - fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) ^ 2 ≤ 64 * K ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDual_physicalDeepVariation_fixedFraction n m hn hm hm2 r hr base K hK hmr hlower hupper


-- created on 2026-10-23
