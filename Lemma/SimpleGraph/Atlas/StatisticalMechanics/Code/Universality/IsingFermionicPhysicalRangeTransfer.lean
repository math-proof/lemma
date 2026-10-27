import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRangeTransfer
open StatMech StatMech.Universality


/--
[fkIsingSquareRadialPatchPrimal_physicalDeepVariation_sq_le_of_ghostComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRangeTransfer.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimal_physicalDeepVariation_sq_le_of_ghostComparison_eq
  {n m : Nat}
  {r : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hr : 0 < r)
  (hprimalLower : ∀ p, 0 ≤ fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p)
  (hdualUpper : ∀ q, fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q ≤ 1) :
-- imply
  ((1 / (m : Real)) * ∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r, |fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.snd - fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.fst|) ^ 2 ≤ 64 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimal_physicalDeepVariation_sq_le_of_ghostComparison n m hn hm hm2 r hr base hprimalLower hdualUpper

/--
[fkIsingSquareRadialPatchDual_physicalDeepVariation_sq_le_of_ghostComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRangeTransfer.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDual_physicalDeepVariation_sq_le_of_ghostComparison_eq
  {n m : Nat}
  {r : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hr : 0 < r)
  (hprimalLower : ∀ p, 0 ≤ fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p)
  (hdualUpper : ∀ q, fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q ≤ 1) :
-- imply
  ((1 / (m : Real)) * ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r, |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd - fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) ^ 2 ≤ 64 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDual_physicalDeepVariation_sq_le_of_ghostComparison n m hn hm hm2 r hr base hprimalLower hdualUpper


-- created on 2026-10-23
