import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCaccioppoli.Part2
open StatMech StatMech.Universality


/--
[fkIsingSquareRadialPatchDualGraph_neighbor_card_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCaccioppoli.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDualGraph_neighbor_card_le_four_eq
  {m : Nat}
  {p : FKIsingSquareRadialPatchDualNode m} :
-- imply
  Nat.card ((fkIsingSquareRadialPatchDualGraph m).neighborSet p) ≤ 4 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDualGraph_neighbor_card_le_four m p

/--
[fkIsingSquareRadialPatchPrimalGraph_neighbor_card_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCaccioppoli.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalGraph_neighbor_card_le_four_eq
  {n m : Nat}
  {p : FKIsingSquareRadialPatchPrimalNode m}
-- given
  (hm : m ≤ n) :
-- imply
  Nat.card ((fkIsingSquareRadialPatchPrimalGraph n m hm).neighborSet p) ≤ 4 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalGraph_neighbor_card_le_four n m hm p

/--
[fkIsingSquareRadialPatchPrimalInteriorCutoff_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCaccioppoli.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalInteriorCutoff_support_eq
  {m : Nat} :
-- imply
  ∀ p, fkIsingSquareRadialPatchPrimalInteriorCutoff m p ≠ 0 → ¬ fkIsingSquareRadialPatchPrimalBoundary m p := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalInteriorCutoff_support m

/--
[fkIsingSquareRadialPatchDualInteriorCutoff_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCaccioppoli.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDualInteriorCutoff_support_eq
  {m : Nat} :
-- imply
  ∀ p, fkIsingSquareRadialPatchDualInteriorCutoff m p ≠ 0 → ¬ fkIsingSquareRadialPatchDualBoundary m p := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDualInteriorCutoff_support m

/--
[fkIsingSquareRadialPatchPrimalInteriorCutoff_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCaccioppoli.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalInteriorCutoff_lipschitz_eq
  {n m : Nat}
  {d : (fkIsingSquareRadialPatchPrimalGraph n m hm).Dart}
-- given
  (hm : m ≤ n) :
-- imply
  |fkIsingSquareRadialPatchPrimalInteriorCutoff m d.snd - fkIsingSquareRadialPatchPrimalInteriorCutoff m d.fst| ≤ 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalInteriorCutoff_lipschitz n m hm d

/--
[fkIsingSquareRadialPatchDualInteriorCutoff_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCaccioppoli.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDualInteriorCutoff_lipschitz_eq
  {m : Nat}
  {d : (fkIsingSquareRadialPatchDualGraph m).Dart} :
-- imply
  |fkIsingSquareRadialPatchDualInteriorCutoff m d.snd - fkIsingSquareRadialPatchDualInteriorCutoff m d.fst| ≤ 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDualInteriorCutoff_lipschitz m d

/--
[fkIsingSquareRadialPatchPrimalInteriorCutoff_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCaccioppoli.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalInteriorCutoff_one_eq
  {n m : Nat}
-- given
  (hm : m ≤ n) :
-- imply
  ∀ d ∈ fkIsingSquareRadialPatchPrimalInteriorDarts n m hm, (1 : Real) ≤ fkIsingSquareRadialPatchPrimalInteriorCutoff m d.snd := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalInteriorCutoff_one n m hm

/--
[fkIsingSquareRadialPatchDualInteriorCutoff_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCaccioppoli.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDualInteriorCutoff_one_eq
  {m : Nat} :
-- imply
  ∀ d ∈ fkIsingSquareRadialPatchDualInteriorDarts m, (1 : Real) ≤ fkIsingSquareRadialPatchDualInteriorCutoff m d.snd := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDualInteriorCutoff_one m

/--
[fkIsingSquareRadialPatchPrimalInteriorCutoff_energy_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCaccioppoli.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalInteriorCutoff_energy_le_eq
  {n m : Nat}
-- given
  (hm : m ≤ n) :
-- imply
  isingFiniteGraphDartSum (fkIsingSquareRadialPatchPrimalGraph n m hm) (fun x y ↦ (fkIsingSquareRadialPatchPrimalInteriorCutoff m y - fkIsingSquareRadialPatchPrimalInteriorCutoff m x) ^ 2) ≤ 4 * (m : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalInteriorCutoff_energy_le n m hm

/--
[fkIsingSquareRadialPatchDualInteriorCutoff_energy_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCaccioppoli.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDualInteriorCutoff_energy_le_eq
  {m : Nat} :
-- imply
  isingFiniteGraphDartSum (fkIsingSquareRadialPatchDualGraph m) (fun x y ↦ (fkIsingSquareRadialPatchDualInteriorCutoff m y - fkIsingSquareRadialPatchDualInteriorCutoff m x) ^ 2) ≤ 4 * (m : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDualInteriorCutoff_energy_le m

/--
[fkIsingSquareRadialPatchPrimitive_mem_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCaccioppoli.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimitive_mem_range_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi : i < m)
  (hj : j < m) :
-- imply
  -(2 * (m : Real)) ≤ fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j ∧ fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j ≤ 2 * (m : Real) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimitive_mem_range n m hn hm hmpos i j hi hj

/--
[fkIsingSquareRadialPatchPrimalValue_mem_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCaccioppoli.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalValue_mem_range_eq
  {n m : Nat}
  {base : Real}
  {p : FKIsingSquareRadialPatchPrimalNode m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m) :
-- imply
  base - 2 * (m : Real) ≤ fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p ∧ fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p ≤ base + 2 * (m : Real) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalValue_mem_range n m hn hm hmpos base p

/--
[fkIsingSquareRadialPatchDualValue_mem_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCaccioppoli.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDualValue_mem_range_eq
  {n m : Nat}
  {base : Real}
  {p : FKIsingSquareRadialPatchDualNode m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m) :
-- imply
  base - 2 * (m : Real) ≤ fkIsingSquareRadialPatchDualValue n m hn hm hmpos base p ∧ fkIsingSquareRadialPatchDualValue n m hn hm hmpos base p ≤ base + 2 * (m : Real) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDualValue_mem_range n m hn hm hmpos base p

/--
[fkIsingSquareRadialPatchDual_interiorVariation_sq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCaccioppoli.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDual_interiorVariation_sq_le_eq
  {n m : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m) :
-- imply
  (∑ d ∈ fkIsingSquareRadialPatchDualInteriorDarts m, |fkIsingSquareRadialPatchDualValue n m hn hm hmpos base d.snd - fkIsingSquareRadialPatchDualValue n m hn hm hmpos base d.fst|) ^ 2 ≤ 256 * (#(fkIsingSquareRadialPatchDualInteriorDarts m) : Real) * (m : Real) ^ 4 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDual_interiorVariation_sq_le n m hn hm hmpos base

/--
[fkIsingSquareRadialPatchPrimal_interiorVariation_sq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCaccioppoli.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimal_interiorVariation_sq_le_eq
  {n m : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m) :
-- imply
  (∑ d ∈ fkIsingSquareRadialPatchPrimalInteriorDarts n m hm, |fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.snd - fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.fst|) ^ 2 ≤ 256 * (#(fkIsingSquareRadialPatchPrimalInteriorDarts n m hm) : Real) * (m : Real) ^ 4 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimal_interiorVariation_sq_le n m hn hm hmpos base


-- created on 2026-10-23
